/-
  Nock/AIR.lean

  M2 spine — the **reified / exportable AIR** (first vertical slice).

  This file turns the proposition-level constraint gates of `Nock/ComputeTable.lean`
  (`RAPcomp`/`Vcomp`, `SVsat`, `evalR`, and the field-arithmetic gate lemmas `gate5`,
  booleanity, …) into **first-class data**: a deep-embedded, field-generic, *serializable*
  AIR (`Expr`/`Constraint`/`AIR`) that is
    (a) **proven equivalent** to the sound Prop-level gates it reflects, and
    (b) **exported** to a backend-neutral format (S-expr / JSON) that a black-box Plonky3
        backend will consume.

  The vertical slice reflects a representative fragment of the compute table:
    (i)  the State-Variables **booleanity** + **one-hot** gates
         (`op_j·(1−op_j)=0`, `Σ op_j = 1`; the paper), and
    (ii) **opcode 5**'s equality gate — the most interesting non-linear gate.

  ─────────────────────────────────────────────────────────────────────────────────────────
  Plonky3 `AirBuilder` mapping (design note)
  ─────────────────────────────────────────────────────────────────────────────────────────
  The `VarKind` taxonomy mirrors the DEPLOYED constraint IR (`MPMega`: CON/VAR/RND/DYN/COM),
  so a future differential diff against the shipped `constraints-2.jam` blob lines up:

    VarKind         Lean `Env` field   Plonky3 `AirBuilder` source
    ───────────     ────────────────   ──────────────────────────────────────────────────
    traceCur        env.trace          `AirBuilder::main` row `local`  (current trace row)
    traceNext       env.traceNext      `AirBuilder::main` row `next`   (transition step)
    challenge       env.chal           permutation / RLC randomness
                                        (`PermutationAirBuilder::permutation_randomness`,
                                         verifier-drawn α,β,γ,z and RLC coeffs a,b,c)
    publicVal       env.pub            `AirBuilder::public_values`     (public/terminal/dyn)

  A `Constraint` asserts `expr = 0`.  `ConstraintKind` maps to how Plonky3 gates the assertion:
    boundary   → `builder.when_first_row`      (first-row / boundary)
    transition → `builder.when_transition`     (uses traceNext)
    terminal   → `builder.when_last_row`
    row        → unconditional `builder.assert_zero(expr)` (holds on every row)

  `Expr.degree` counts degree **in trace variables only** (`challenge`/`publicVal`/`Const`
  are degree 0) — this is exactly the AIR constraint degree Plonky3 needs for its quotient /
  DEEP-ALI bookkeeping.  Coefficients are `ℤ` (`Const`): our gates use only small integer
  coefficients; the verifier randomness / RLC coefficients are *variables* (`challenge`),
  never baked-in constants — so the exported `Expr` is genuinely field-free symbolic data.

  ─────────────────────────────────────────────────────────────────────────────────────────
  Faithfulness posture
  ─────────────────────────────────────────────────────────────────────────────────────────
  For every reflected gate we prove that its `Expr.eval env = 0` (at an `env` decoded from the
  compute row's `Inputs/Pub/Dec/Extra`) is EQUIVALENT to the existing Prop-level gate in
  `ComputeTable`.  The `eval`-vs-gate biconditionals (`reified_sv_bool_sound`,
  `reified_onehot_sound`, `reified_gate5_sound`) are TIGHT and side-condition-free — the deep
  embedding computes the exact same polynomial.  We additionally reuse `gate5` /
  `opSel_boolean` / `opSel_oneHot` to tie the reflected slice to the *honest* Nock semantics
  (`reified_gate5_semantics`, `opSel_satisfies_sv`).  Everything is generic over the field `K`;
  the `AIR` export data is `K`-free.
-/
import Nock.ComputeTable
import Nock.MemoryTable
import Nock.Walk
import Nock.IO
import Nock.NockVM

namespace Nock
namespace Reified

open ComputeTable
open Classical
attribute [local instance] Classical.propDecidable

/-! ## 1. The deep embedding (field-generic, exportable) -/

/-- Variable taxonomy, mirroring the deployed constraint-IR (`MPMega` CON/VAR/RND/DYN/COM) and
    Plonky3's `AirBuilder` sources (see file docstring).  `publicVal` is the paper's "public"
    kind (`public` is a reserved keyword in Lean). -/
inductive VarKind
  | traceCur    -- current-row trace column   → AirBuilder main `local`
  | traceNext   -- next-row trace column       → AirBuilder main `next` (transition)
  | challenge   -- verifier randomness α,β,γ,z + RLC coeffs a,b,c → permutation randomness
  | publicVal   -- public / terminal / dynamic inputs → AirBuilder public values
deriving DecidableEq, Repr

/-- The deep-embedded constraint expression.  Coefficients are `ℤ` (`Const`); challenges and
    RLC coefficients are *variables* (`Var.challenge _`), never constants. -/
inductive Expr
  | Var (kind : VarKind) (idx : ℕ)
  | Const (c : ℤ)
  | Add (a b : Expr)
  | Sub (a b : Expr)
  | Mul (a b : Expr)
  | Neg (a : Expr)
  | Pow (e : Expr) (n : ℕ)
deriving Repr

/-- A per-`VarKind` valuation supplying the field value of each column/randomness/public slot. -/
structure Env (K : Type*) where
  trace     : ℕ → K
  traceNext : ℕ → K
  chal      : ℕ → K
  pub       : ℕ → K

/-- Evaluate a symbolic expression in a field `K` under an environment.  `Const c ↦ (c : K)`
    via the integer cast. -/
def Expr.eval {K : Type*} [Field K] : Expr → Env K → K
  | .Var .traceCur i,  env => env.trace i
  | .Var .traceNext i, env => env.traceNext i
  | .Var .challenge i, env => env.chal i
  | .Var .publicVal i, env => env.pub i
  | .Const c,          _   => (c : K)
  | .Add a b,          env => a.eval env + b.eval env
  | .Sub a b,          env => a.eval env - b.eval env
  | .Mul a b,          env => a.eval env * b.eval env
  | .Neg a,            env => - a.eval env
  | .Pow e n,          env => (e.eval env) ^ n

/-- A challenge or constant base contributes degree 0 for any exponent, including an
    abstract `Nat.size (ringChar K)`. Matching on the base degree avoids reducing that
    exponent. -/
def Expr.powDegree : ℕ → ℕ → ℕ
  | 0, _ => 0
  | d + 1, n => (d + 1) * n

/-- Total degree **in trace variables only** — the AIR constraint degree Plonky3 needs.
    `Const`/`challenge`/`publicVal` are degree 0; `traceCur`/`traceNext` are degree 1. -/
def Expr.degree : Expr → ℕ
  | .Var .traceCur _  => 1
  | .Var .traceNext _ => 1
  | .Var .challenge _ => 0
  | .Var .publicVal _ => 0
  | .Const _          => 0
  | .Add a b          => max a.degree b.degree
  | .Sub a b          => max a.degree b.degree
  | .Mul a b          => a.degree + b.degree
  | .Neg a            => a.degree
  | .Pow e n          => Expr.powDegree e.degree n

/-- How a constraint is gated (see the Plonky3 mapping in the file docstring). -/
inductive ConstraintKind
  | boundary | transition | terminal | row
deriving DecidableEq, Repr

/-- A single AIR constraint, asserting `expr = 0`. -/
structure Constraint where
  kind : ConstraintKind
  expr : Expr

/-- The constraint's degree (its expression's trace-degree). -/
def Constraint.degree (c : Constraint) : ℕ := c.expr.degree

/-- A backend-neutral AIR: the shape of the trace/randomness/public interface plus the list of
    constraints.  This is `K`-free symbolic data — exactly what gets serialized. -/
structure AIR where
  numTraceCols  : ℕ
  numChallenges : ℕ
  numPublic     : ℕ
  constraints   : List Constraint

/-- The maximum constraint degree of the AIR (Plonky3 quotient-degree bookkeeping). -/
def AIR.maxDegree (air : AIR) : ℕ :=
  air.constraints.foldr (fun c acc => max c.expr.degree acc) 0

/-! ## 2. The reflected slice: column layout, expressions, and the decoded environment

  Trace-column layout (`numTraceCols = 19`):
    0 … 9   : one-hot opcode selectors `op_0 … op_9`
    10      : `op_cons` (`op_11`)
    11      : `ev` (`e.leaf`, the OP_5 equality output bit)
    12,13,14: `sf1_e.(size,dyck,leaf)`   (first subformula evaluation fingerprint)
    15,16,17: `sf2_e.(size,dyck,leaf)`   (second subformula evaluation fingerprint)
    18      : `inv_gen` (the OP_5 RLC inverse witness `g`)
  Challenge columns (`numChallenges = 3`): 0 = `a`, 1 = `b`, 2 = `c`  (OP_5 RLC coefficients).
  Public columns (`numPublic = 0`): unused by this slice. -/

/-- Column index of each opcode's one-hot selector. -/
def opCol : State → ℕ
  | .s0 => 0 | .s1 => 1 | .s2 => 2 | .s3 => 3 | .s4 => 4
  | .s5 => 5 | .s6 => 6 | .s7 => 7 | .s8 => 8 | .s9 => 9 | .cons => 10

/-- The environment decoded from a compute row.  `op : State → K` is the one-hot selector
    valuation (a free column in the AIR; the honest assignment is `opSel pub.state`); the OP_5
    columns are read off `pub`/`ex`, the RLC coefficients off `inp`. -/
def computeEnv {K : Type*} [Field K]
    (inp : Inputs K) (op : State → K) (pub : Pub K) (ex : Extra K) : Env K where
  trace := fun i => match i with
    | 0 => op .s0 | 1 => op .s1 | 2 => op .s2 | 3 => op .s3 | 4 => op .s4
    | 5 => op .s5 | 6 => op .s6 | 7 => op .s7 | 8 => op .s8 | 9 => op .s9 | 10 => op .cons
    | 11 => pub.e.leaf
    | 12 => pub.sf1_e.size | 13 => pub.sf1_e.dyck | 14 => pub.sf1_e.leaf
    | 15 => pub.sf2_e.size | 16 => pub.sf2_e.dyck | 17 => pub.sf2_e.leaf
    | 18 => ex.invGen
    | _  => 0
  traceNext := fun _ => 0
  chal := fun i => match i with
    | 0 => inp.a | 1 => inp.b | 2 => inp.c | _ => 0
  pub := fun _ => 0

/-! ### The reflected expressions -/

/-- SV booleanity gate for the selector in column `i`: `op_i · (1 − op_i)`. -/
def svBoolExpr (i : ℕ) : Expr :=
  .Mul (.Var .traceCur i) (.Sub (.Const 1) (.Var .traceCur i))

/-- SV one-hot gate: `(Σ_{i=0}^{10} op_i) − 1`. -/
def svOneHotExpr : Expr :=
  .Sub
    (.Add (.Var .traceCur 0) (.Add (.Var .traceCur 1) (.Add (.Var .traceCur 2)
     (.Add (.Var .traceCur 3) (.Add (.Var .traceCur 4) (.Add (.Var .traceCur 5)
     (.Add (.Var .traceCur 6) (.Add (.Var .traceCur 7) (.Add (.Var .traceCur 8)
     (.Add (.Var .traceCur 9) (.Var .traceCur 10)))))))))))
    (.Const 1)

/-- `d1 = sf1_e.size − sf2_e.size`. -/
def d1Expr : Expr := .Sub (.Var .traceCur 12) (.Var .traceCur 15)
/-- `d2 = sf1_e.dyck − sf2_e.dyck`. -/
def d2Expr : Expr := .Sub (.Var .traceCur 13) (.Var .traceCur 16)
/-- `d3 = sf1_e.leaf − sf2_e.leaf`. -/
def d3Expr : Expr := .Sub (.Var .traceCur 14) (.Var .traceCur 17)
/-- `1 − ev`. -/
def oneMinusEv : Expr := .Sub (.Const 1) (.Var .traceCur 11)

/-- OP_5 gate EC.5.1: booleanity of `ev`, `ev·(1−ev)`. -/
def g5BoolExpr : Expr := .Mul (.Var .traceCur 11) oneMinusEv
/-- OP_5 gate EC.5.2: `(1−ev)·d1`. -/
def g5D1Expr : Expr := .Mul oneMinusEv d1Expr
/-- OP_5 gate EC.5.3: `(1−ev)·d2`. -/
def g5D2Expr : Expr := .Mul oneMinusEv d2Expr
/-- OP_5 gate EC.5.4: `(1−ev)·d3`. -/
def g5D3Expr : Expr := .Mul oneMinusEv d3Expr
/-- The RLC `a·d1 + b·d2 + c·d3 + (1−ev)`. -/
def rlcExpr : Expr :=
  .Add (.Add (.Add (.Mul (.Var .challenge 0) d1Expr) (.Mul (.Var .challenge 1) d2Expr))
             (.Mul (.Var .challenge 2) d3Expr))
       oneMinusEv
/-- OP_5 gate EC.5.5: the non-degeneracy inverse, `inv_gen·(RLC) − 1`. -/
def g5RlcExpr : Expr := .Sub (.Mul (.Var .traceCur 18) rlcExpr) (.Const 1)

/-- **The reflected slice `computeAIR_slice`.**  The 11 SV booleanity gates, the SV one-hot
    gate, and the five OP_5 equality gates — all row-local constraints. -/
def computeAIR_slice : AIR where
  numTraceCols  := 19
  numChallenges := 3
  numPublic     := 0
  constraints :=
    ((List.range 11).map (fun i => (⟨.row, svBoolExpr i⟩ : Constraint))) ++
    [ ⟨.row, svOneHotExpr⟩,
      ⟨.row, g5BoolExpr⟩,
      ⟨.row, g5D1Expr⟩,
      ⟨.row, g5D2Expr⟩,
      ⟨.row, g5D3Expr⟩,
      ⟨.row, g5RlcExpr⟩ ]

/-! ## 3. Reflection faithfulness (the crux) -/

variable {K : Type*} [Field K]

/-- Per-opcode SV booleanity: the reflected gate evaluates to the honest field expression. -/
theorem svBoolExpr_eval (inp : Inputs K) (op : State → K) (pub : Pub K) (ex : Extra K)
    (j : State) :
    (svBoolExpr (opCol j)).eval (computeEnv inp op pub ex) = op j * (1 - op j) := by
  cases j <;> simp [svBoolExpr, opCol, Expr.eval, computeEnv]

/-- **`reified_sv_bool_sound` (biconditional).**  The reflected SV booleanity gates evaluate to
    zero (for every opcode column) iff the existing Prop-level SV2 booleanity gate holds. -/
theorem reified_sv_bool_sound (inp : Inputs K) (op : State → K) (pub : Pub K) (ex : Extra K) :
    (∀ j : State, (svBoolExpr (opCol j)).eval (computeEnv inp op pub ex) = 0)
      ↔ (∀ j : State, op j * (1 - op j) = 0) := by
  constructor <;> intro h j
  · rw [← svBoolExpr_eval inp op pub ex j]; exact h j
  · rw [svBoolExpr_eval inp op pub ex j]; exact h j

/-- **`reified_onehot_sound` (biconditional).**  The reflected SV one-hot gate evaluates to zero
    iff the existing Prop-level SV3 one-hot gate `op cons + Σ_{0}^{9} op = 1` holds. -/
theorem reified_onehot_sound (inp : Inputs K) (op : State → K) (pub : Pub K) (ex : Extra K) :
    svOneHotExpr.eval (computeEnv inp op pub ex) = 0
      ↔ (op State.cons + sum09 op = 1) := by
  simp only [svOneHotExpr, Expr.eval, computeEnv, Int.cast_one, sum09]
  constructor <;> intro h <;> linear_combination h

/-- **`reified_gate5_sound` (tight biconditional).**  The five reflected OP_5 gates evaluate to
    zero iff the existing Prop-level `evalR.s5` gate body holds (with `inv_gen := ex.invGen`).
    Side-condition-free: the deep embedding computes the identical polynomial. -/
theorem reified_gate5_sound (inp : Inputs K) (op : State → K) (pub : Pub K) (ex : Extra K) :
    (g5BoolExpr.eval (computeEnv inp op pub ex) = 0 ∧
     g5D1Expr.eval (computeEnv inp op pub ex) = 0 ∧
     g5D2Expr.eval (computeEnv inp op pub ex) = 0 ∧
     g5D3Expr.eval (computeEnv inp op pub ex) = 0 ∧
     g5RlcExpr.eval (computeEnv inp op pub ex) = 0)
      ↔ (pub.e.leaf * (1 - pub.e.leaf) = 0 ∧
         (1 - pub.e.leaf) * (pub.sf1_e.size - pub.sf2_e.size) = 0 ∧
         (1 - pub.e.leaf) * (pub.sf1_e.dyck - pub.sf2_e.dyck) = 0 ∧
         (1 - pub.e.leaf) * (pub.sf1_e.leaf - pub.sf2_e.leaf) = 0 ∧
         ex.invGen * (inp.a * (pub.sf1_e.size - pub.sf2_e.size)
             + inp.b * (pub.sf1_e.dyck - pub.sf2_e.dyck)
             + inp.c * (pub.sf1_e.leaf - pub.sf2_e.leaf) + (1 - pub.e.leaf)) = 1) := by
  simp only [g5BoolExpr, g5D1Expr, g5D2Expr, g5D3Expr, g5RlcExpr, oneMinusEv, d1Expr, d2Expr,
    d3Expr, rlcExpr, Expr.eval, computeEnv, Int.cast_one]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨by linear_combination h1, by linear_combination h2, by linear_combination h3,
           by linear_combination h4, by linear_combination h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨by linear_combination h1, by linear_combination h2, by linear_combination h3,
           by linear_combination h4, by linear_combination h5⟩

/-- **`reified_gate5_semantics`.**  Tying the reflected OP_5 slice to the *honest* Nock equality
    result via the existing `gate5` lemma: for a non-degenerate RLC (`hnd`, the paper's random
    `a,b,c`), the five reflected gates are satisfiable (over the free inverse column `inv_gen`)
    iff `ev` equals the honest equality bit `⟦(d1,d2,d3) ≠ 0⟧`.  This is the genuine
    "AIR gate ⟺ semantics" faithfulness statement, mirroring `ComputeTable.eval_iff`. -/
theorem reified_gate5_semantics (inp : Inputs K) (op : State → K) (pub : Pub K) (consInv : K)
    (hnd : ¬(pub.sf1_e.size - pub.sf2_e.size = 0 ∧ pub.sf1_e.dyck - pub.sf2_e.dyck = 0
              ∧ pub.sf1_e.leaf - pub.sf2_e.leaf = 0) →
        inp.a * (pub.sf1_e.size - pub.sf2_e.size) + inp.b * (pub.sf1_e.dyck - pub.sf2_e.dyck)
          + inp.c * (pub.sf1_e.leaf - pub.sf2_e.leaf) ≠ 0) :
    (∃ g : K,
        g5BoolExpr.eval (computeEnv inp op pub ⟨consInv, g⟩) = 0 ∧
        g5D1Expr.eval (computeEnv inp op pub ⟨consInv, g⟩) = 0 ∧
        g5D2Expr.eval (computeEnv inp op pub ⟨consInv, g⟩) = 0 ∧
        g5D3Expr.eval (computeEnv inp op pub ⟨consInv, g⟩) = 0 ∧
        g5RlcExpr.eval (computeEnv inp op pub ⟨consInv, g⟩) = 0)
      ↔ pub.e.leaf = (if (pub.sf1_e.size - pub.sf2_e.size = 0
            ∧ pub.sf1_e.dyck - pub.sf2_e.dyck = 0 ∧ pub.sf1_e.leaf - pub.sf2_e.leaf = 0)
          then 0 else 1) := by
  constructor
  · rintro ⟨g, hconj⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := (reified_gate5_sound inp op pub ⟨consInv, g⟩).mp hconj
    exact (gate5 inp.a inp.b inp.c _ _ _ pub.e.leaf hnd).mp ⟨h1, h2, h3, h4, g, h5⟩
  · intro hev
    obtain ⟨h1, h2, h3, h4, w, h5⟩ :=
      (gate5 inp.a inp.b inp.c _ _ _ pub.e.leaf hnd).mpr hev
    exact ⟨w, (reified_gate5_sound inp op pub ⟨consInv, w⟩).mpr ⟨h1, h2, h3, h4, h5⟩⟩

/-- **Non-vacuity / reuse.**  The honest one-hot assignment `op := opSel pub.state` makes every
    reflected SV gate evaluate to zero — reusing `opSel_boolean` / `opSel_oneHot`.  So the
    reflected SV constraints are genuinely satisfiable (not vacuously true). -/
theorem opSel_satisfies_sv (inp : Inputs K) (pub : Pub K) (ex : Extra K) :
    (∀ j : State, (svBoolExpr (opCol j)).eval (computeEnv inp (opSel pub.state) pub ex) = 0)
      ∧ svOneHotExpr.eval (computeEnv inp (opSel pub.state) pub ex) = 0 := by
  refine ⟨(reified_sv_bool_sound inp _ pub ex).mpr ?_,
          (reified_onehot_sound inp _ pub ex).mpr ?_⟩
  · exact opSel_boolean pub.state
  · exact opSel_oneHot pub.state

/-! ### Degree accounting (all slice constraints are degree ≤ 2) -/

theorem svBoolExpr_degree (i : ℕ) : (svBoolExpr i).degree = 2 := rfl
theorem svOneHotExpr_degree : svOneHotExpr.degree = 1 := rfl
theorem g5BoolExpr_degree : g5BoolExpr.degree = 2 := rfl
theorem g5D1Expr_degree : g5D1Expr.degree = 2 := rfl
theorem g5RlcExpr_degree : g5RlcExpr.degree = 2 := rfl

/-- The slice's max constraint degree is `2` — matching the hand-known degree of the SV
    booleanity and OP_5 gates (booleanity is degree 2; the RLC-inverse gate is degree 2 because
    challenges `a,b,c` are degree 0). -/
theorem slice_maxDegree : computeAIR_slice.maxDegree = 2 := by rfl

/-! ## 3b. The COMPLETE per-row compute-table AIR

  This section scales the vertical slice to the **entire per-row compute table** `RAPcomp`
  of `Nock/ComputeTable.lean`: the formula decomposition, memory record 1,
  the full State-Variables block (SV2–SV6), the per-opcode memory-record block (`memBlk`), and
  the per-opcode evaluation block (`evalR`) for ALL eleven opcodes `OP_0..OP_9 + cons`.

  ─────────────────────────────────────────────────────────────────────────────────────────
  FULL TRACE-COLUMN LAYOUT (`numTraceCols = 94`).  Each fingerprint `FP` occupies three
  consecutive columns `(size, dyck, leaf)`; each memory record `MemRec` occupies eight
  `(root.size,root.dyck,root.leaf, child.size,child.dyck,child.leaf, axis, ts)`.

      0 … 9   op_0 … op_9      one-hot opcode selectors
      10      op_cons          (op_11)
      11–13   pub.s            input subject fingerprint
      14–16   pub.f            input formula fingerprint
      17–19   pub.e            evaluation fingerprint
      20–22   pub.sf1_s        subformula-1 child subject
      23–25   pub.sf1_f        subformula-1 child formula
      26–28   pub.sf1_e        subformula-1 evaluation
      29–31   pub.sf2_s        subformula-2 child subject
      32–34   pub.sf2_f        subformula-2 child formula
      35–37   pub.sf2_e        subformula-2 evaluation
      38–40   pub.sf3_s        subformula-3 child subject
      41–43   pub.sf3_f        subformula-3 child formula
      44–46   pub.sf3_e        subformula-3 evaluation
      47–49   dec.f_h          formula-head
      50–52   dec.f_t          formula-tail
      53–55   dec.f_th
      56–58   dec.f_tt
      59–61   dec.f_tth
      62–64   dec.f_ttt
      65      pub.ln_prev      log-nonce recurrence
      66      pub.ln
      67–74   pub.mr1          memory record 1  (root 67–69, child 70–72, axis 73, ts 74)
      75–82   pub.mr2          memory record 2
      83–90   pub.mr3          memory record 3
      91      ex.consInv       SV5 inverse witness (`cons_inv`)
      92      ex.invGen        generalized-inverse witness (`inv_gen`, EC.3/EC.5/EC.8/EC.11)
      93      zinv             `z⁻¹` witness column (see the FP.cons note below)

  Challenge columns (`numChallenges = 5`): 0 = α, 1 = z, 2 = a, 3 = b, 4 = c.
  Public columns (`numPublic = 0`).

  ─────────────────────────────────────────────────────────────────────────────────────────
  FP.cons  and the  `z⁻¹`  WITNESS  (design note, deliverable #2)
  ─────────────────────────────────────────────────────────────────────────────────────────
  `FP.cons`'s dyck component is
      dyck = z·a.dyck + a.size²·z⁻¹ + a.size²·b.dyck,
  which contains `z⁻¹` — NOT a polynomial.  Every `FP.cons` dyck constraint uses the **column** `zinv`, never `z⁻¹`.
  The gate `z·zinv = 1` forces `zinv = z⁻¹` for any `z ≠ 0` (and is unsatisfiable when `z = 0`),
  so an honest prover can only fill `zinv := z⁻¹`. -/

/-! ### FP-level symbolic expressions (a triple of `Expr`) -/

/-- A fingerprint built from three symbolic expressions `(size, dyck, leaf)`. Pure `K`-free data. -/
structure FPExpr where
  size : Expr
  dyck : Expr
  leaf : Expr

/-- A memory record built from symbolic expressions. Pure `K`-free data. -/
structure MemRecExpr where
  root  : FPExpr
  child : FPExpr
  axis  : Expr
  ts    : Expr

/-- Shorthand: a current-row trace-column variable. -/
def tc (i : ℕ) : Expr := .Var .traceCur i
/-- Shorthand: a challenge variable. -/
def chl (i : ℕ) : Expr := .Var .challenge i
/-- The `FPExpr` reading the three consecutive trace columns based at `base`. -/
def fpCol (base : ℕ) : FPExpr := ⟨tc base, tc (base + 1), tc (base + 2)⟩
/-- The `MemRecExpr` reading the eight consecutive columns based at `base`. -/
def mrCol (base : ℕ) : MemRecExpr :=
  ⟨fpCol base, fpCol (base + 3), tc (base + 6), tc (base + 7)⟩

variable {K : Type*} [Field K]

/-- Evaluate an `FPExpr` to a concrete fingerprint. -/
def FPExpr.eval (a : FPExpr) (env : Env K) : FP K :=
  ⟨a.size.eval env, a.dyck.eval env, a.leaf.eval env⟩

/-- Evaluate a `MemRecExpr` to a concrete memory record. -/
def MemRecExpr.eval (m : MemRecExpr) (env : Env K) : MemRec K :=
  ⟨m.root.eval env, m.child.eval env, m.axis.eval env, m.ts.eval env⟩

/-! ### Named FP / MemRec readers (columns above) -/

def cS   : FPExpr := fpCol 11
def cF   : FPExpr := fpCol 14
def cE   : FPExpr := fpCol 17
def cSf1s : FPExpr := fpCol 20
def cSf1f : FPExpr := fpCol 23
def cSf1e : FPExpr := fpCol 26
def cSf2s : FPExpr := fpCol 29
def cSf2f : FPExpr := fpCol 32
def cSf2e : FPExpr := fpCol 35
def cSf3s : FPExpr := fpCol 38
def cSf3f : FPExpr := fpCol 41
def cSf3e : FPExpr := fpCol 44
def cFh  : FPExpr := fpCol 47
def cFt  : FPExpr := fpCol 50
def cFth : FPExpr := fpCol 53
def cFtt : FPExpr := fpCol 56
def cFtth : FPExpr := fpCol 59
def cFttt : FPExpr := fpCol 62
def cMr1 : MemRecExpr := mrCol 67
def cMr2 : MemRecExpr := mrCol 75
def cMr3 : MemRecExpr := mrCol 83

/-- The environment decoded from a full compute row.  `op : State → K` is the free one-hot
    selector valuation (honest assignment `opSel pub.state`); every other column is read off
    `pub`/`dec`/`ex`/`inp`.  The `zinv` column (93) is instantiated at the honest witness value
    `inp.z⁻¹` (see the FP.cons design note). -/
def computeEnvFull
    (inp : Inputs K) (op : State → K) (pub : Pub K) (dec : Dec K) (ex : Extra K) : Env K where
  trace := fun i => match i with
    | 0 => op .s0 | 1 => op .s1 | 2 => op .s2 | 3 => op .s3 | 4 => op .s4
    | 5 => op .s5 | 6 => op .s6 | 7 => op .s7 | 8 => op .s8 | 9 => op .s9 | 10 => op .cons
    | 11 => pub.s.size | 12 => pub.s.dyck | 13 => pub.s.leaf
    | 14 => pub.f.size | 15 => pub.f.dyck | 16 => pub.f.leaf
    | 17 => pub.e.size | 18 => pub.e.dyck | 19 => pub.e.leaf
    | 20 => pub.sf1_s.size | 21 => pub.sf1_s.dyck | 22 => pub.sf1_s.leaf
    | 23 => pub.sf1_f.size | 24 => pub.sf1_f.dyck | 25 => pub.sf1_f.leaf
    | 26 => pub.sf1_e.size | 27 => pub.sf1_e.dyck | 28 => pub.sf1_e.leaf
    | 29 => pub.sf2_s.size | 30 => pub.sf2_s.dyck | 31 => pub.sf2_s.leaf
    | 32 => pub.sf2_f.size | 33 => pub.sf2_f.dyck | 34 => pub.sf2_f.leaf
    | 35 => pub.sf2_e.size | 36 => pub.sf2_e.dyck | 37 => pub.sf2_e.leaf
    | 38 => pub.sf3_s.size | 39 => pub.sf3_s.dyck | 40 => pub.sf3_s.leaf
    | 41 => pub.sf3_f.size | 42 => pub.sf3_f.dyck | 43 => pub.sf3_f.leaf
    | 44 => pub.sf3_e.size | 45 => pub.sf3_e.dyck | 46 => pub.sf3_e.leaf
    | 47 => dec.f_h.size | 48 => dec.f_h.dyck | 49 => dec.f_h.leaf
    | 50 => dec.f_t.size | 51 => dec.f_t.dyck | 52 => dec.f_t.leaf
    | 53 => dec.f_th.size | 54 => dec.f_th.dyck | 55 => dec.f_th.leaf
    | 56 => dec.f_tt.size | 57 => dec.f_tt.dyck | 58 => dec.f_tt.leaf
    | 59 => dec.f_tth.size | 60 => dec.f_tth.dyck | 61 => dec.f_tth.leaf
    | 62 => dec.f_ttt.size | 63 => dec.f_ttt.dyck | 64 => dec.f_ttt.leaf
    | 65 => pub.ln_prev | 66 => pub.ln
    | 67 => pub.mr1.root.size | 68 => pub.mr1.root.dyck | 69 => pub.mr1.root.leaf
    | 70 => pub.mr1.child.size | 71 => pub.mr1.child.dyck | 72 => pub.mr1.child.leaf
    | 73 => pub.mr1.axis | 74 => pub.mr1.ts
    | 75 => pub.mr2.root.size | 76 => pub.mr2.root.dyck | 77 => pub.mr2.root.leaf
    | 78 => pub.mr2.child.size | 79 => pub.mr2.child.dyck | 80 => pub.mr2.child.leaf
    | 81 => pub.mr2.axis | 82 => pub.mr2.ts
    | 83 => pub.mr3.root.size | 84 => pub.mr3.root.dyck | 85 => pub.mr3.root.leaf
    | 86 => pub.mr3.child.size | 87 => pub.mr3.child.dyck | 88 => pub.mr3.child.leaf
    | 89 => pub.mr3.axis | 90 => pub.mr3.ts
    | 91 => ex.consInv | 92 => ex.invGen | 93 => inp.z⁻¹
    | _ => 0
  traceNext := fun _ => 0
  chal := fun i => match i with
    | 0 => inp.α | 1 => inp.z | 2 => inp.a | 3 => inp.b | 4 => inp.c | _ => 0
  pub := fun _ => 0

/-! ### Reader eval lemmas (each holds by `rfl` via structure-eta through the column match) -/

variable (inp : Inputs K) (op : State → K) (pub : Pub K) (dec : Dec K) (ex : Extra K)

@[simp] theorem eval_cS   : cS.eval   (computeEnvFull inp op pub dec ex) = pub.s := rfl
@[simp] theorem eval_cF   : cF.eval   (computeEnvFull inp op pub dec ex) = pub.f := rfl
@[simp] theorem eval_cE   : cE.eval   (computeEnvFull inp op pub dec ex) = pub.e := rfl
@[simp] theorem eval_cSf1s : cSf1s.eval (computeEnvFull inp op pub dec ex) = pub.sf1_s := rfl
@[simp] theorem eval_cSf1f : cSf1f.eval (computeEnvFull inp op pub dec ex) = pub.sf1_f := rfl
@[simp] theorem eval_cSf1e : cSf1e.eval (computeEnvFull inp op pub dec ex) = pub.sf1_e := rfl
@[simp] theorem eval_cSf2s : cSf2s.eval (computeEnvFull inp op pub dec ex) = pub.sf2_s := rfl
@[simp] theorem eval_cSf2f : cSf2f.eval (computeEnvFull inp op pub dec ex) = pub.sf2_f := rfl
@[simp] theorem eval_cSf2e : cSf2e.eval (computeEnvFull inp op pub dec ex) = pub.sf2_e := rfl
@[simp] theorem eval_cSf3s : cSf3s.eval (computeEnvFull inp op pub dec ex) = pub.sf3_s := rfl
@[simp] theorem eval_cSf3f : cSf3f.eval (computeEnvFull inp op pub dec ex) = pub.sf3_f := rfl
@[simp] theorem eval_cSf3e : cSf3e.eval (computeEnvFull inp op pub dec ex) = pub.sf3_e := rfl
@[simp] theorem eval_cFh  : cFh.eval  (computeEnvFull inp op pub dec ex) = dec.f_h := rfl
@[simp] theorem eval_cFt  : cFt.eval  (computeEnvFull inp op pub dec ex) = dec.f_t := rfl
@[simp] theorem eval_cFth : cFth.eval (computeEnvFull inp op pub dec ex) = dec.f_th := rfl
@[simp] theorem eval_cFtt : cFtt.eval (computeEnvFull inp op pub dec ex) = dec.f_tt := rfl
@[simp] theorem eval_cFtth : cFtth.eval (computeEnvFull inp op pub dec ex) = dec.f_tth := rfl
@[simp] theorem eval_cFttt : cFttt.eval (computeEnvFull inp op pub dec ex) = dec.f_ttt := rfl
@[simp] theorem eval_cMr1 : cMr1.eval (computeEnvFull inp op pub dec ex) = pub.mr1 := rfl
@[simp] theorem eval_cMr2 : cMr2.eval (computeEnvFull inp op pub dec ex) = pub.mr2 := rfl
@[simp] theorem eval_cMr3 : cMr3.eval (computeEnvFull inp op pub dec ex) = pub.mr3 := rfl

/-- Selector-column reader: column `opCol j` evaluates to `op j`. -/
@[simp] theorem eval_op (j : State) :
    (tc (opCol j)).eval (computeEnvFull inp op pub dec ex) = op j := by cases j <;> rfl

@[simp] theorem eval_chAlpha : (chl 0).eval (computeEnvFull inp op pub dec ex) = inp.α := rfl
@[simp] theorem eval_chZ : (chl 1).eval (computeEnvFull inp op pub dec ex) = inp.z := rfl
@[simp] theorem eval_chA : (chl 2).eval (computeEnvFull inp op pub dec ex) = inp.a := rfl
@[simp] theorem eval_chB : (chl 3).eval (computeEnvFull inp op pub dec ex) = inp.b := rfl
@[simp] theorem eval_chC : (chl 4).eval (computeEnvFull inp op pub dec ex) = inp.c := rfl
@[simp] theorem eval_lnPrev : (tc 65).eval (computeEnvFull inp op pub dec ex) = pub.ln_prev := rfl
@[simp] theorem eval_ln : (tc 66).eval (computeEnvFull inp op pub dec ex) = pub.ln := rfl
@[simp] theorem eval_consInv : (tc 91).eval (computeEnvFull inp op pub dec ex) = ex.consInv := rfl
@[simp] theorem eval_invGen : (tc 92).eval (computeEnvFull inp op pub dec ex) = ex.invGen := rfl
@[simp] theorem eval_zinv : (tc 93).eval (computeEnvFull inp op pub dec ex) = inp.z⁻¹ := rfl

/-! ### FP / MemRec component projection (push `.X.eval` through to the concrete value) -/

@[simp] theorem FPExpr.eval_size (a : FPExpr) (env : Env K) :
    a.size.eval env = (a.eval env).size := rfl
@[simp] theorem FPExpr.eval_dyck (a : FPExpr) (env : Env K) :
    a.dyck.eval env = (a.eval env).dyck := rfl
@[simp] theorem FPExpr.eval_leaf (a : FPExpr) (env : Env K) :
    a.leaf.eval env = (a.eval env).leaf := rfl
@[simp] theorem MemRecExpr.eval_root (m : MemRecExpr) (env : Env K) :
    m.root.eval env = (m.eval env).root := rfl
@[simp] theorem MemRecExpr.eval_child (m : MemRecExpr) (env : Env K) :
    m.child.eval env = (m.eval env).child := rfl
@[simp] theorem MemRecExpr.eval_axis (m : MemRecExpr) (env : Env K) :
    m.axis.eval env = (m.eval env).axis := rfl
@[simp] theorem MemRecExpr.eval_ts (m : MemRecExpr) (env : Env K) :
    m.ts.eval env = (m.eval env).ts := rfl

/-! ### Constraint-list gadgets and their soundness -/

/-- Three constraints asserting the fingerprint equality `a = b` (componentwise). -/
def fpEqC (a b : FPExpr) : List Expr :=
  [.Sub a.size b.size, .Sub a.dyck b.dyck, .Sub a.leaf b.leaf]

/-- Three constraints asserting `a = 0` (each component vanishes). -/
def fpZeroC (a : FPExpr) : List Expr := [a.size, a.dyck, a.leaf]

/-- Eight constraints asserting the memory-record equality `m = n`. -/
def memEqC (m n : MemRecExpr) : List Expr :=
  fpEqC m.root n.root ++ fpEqC m.child n.child ++ [.Sub m.axis n.axis, .Sub m.ts n.ts]

/-- Eight constraints asserting `m = MemRec.zero`. -/
def memZeroC (m : MemRecExpr) : List Expr :=
  fpZeroC m.root ++ fpZeroC m.child ++ [m.axis, m.ts]

theorem fpEqC_sound (a b : FPExpr) (env : Env K) :
    (∀ e ∈ fpEqC a b, e.eval env = 0) ↔ a.eval env = b.eval env := by
  simp only [fpEqC, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Expr.eval, sub_eq_zero, FP.ext_iff, FPExpr.eval_size, FPExpr.eval_dyck, FPExpr.eval_leaf]

theorem fpZeroC_sound (a : FPExpr) (env : Env K) :
    (∀ e ∈ fpZeroC a, e.eval env = 0) ↔ a.eval env = 0 := by
  simp only [fpZeroC, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    FP.ext_iff, FPExpr.eval_size, FPExpr.eval_dyck, FPExpr.eval_leaf, FP.zero_size, FP.zero_dyck,
    FP.zero_leaf]

theorem memEqC_sound (m n : MemRecExpr) (env : Env K) :
    (∀ e ∈ memEqC m n, e.eval env = 0) ↔ m.eval env = n.eval env := by
  simp only [memEqC, List.forall_mem_append]
  rw [fpEqC_sound, fpEqC_sound]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Expr.eval,
    sub_eq_zero, MemRec.ext_iff, MemRecExpr.eval_root, MemRecExpr.eval_child,
    MemRecExpr.eval_axis, MemRecExpr.eval_ts]
  tauto

theorem memZeroC_sound (m : MemRecExpr) (env : Env K) :
    (∀ e ∈ memZeroC m, e.eval env = 0) ↔ m.eval env = MemRec.zero := by
  simp only [memZeroC, List.forall_mem_append]
  rw [fpZeroC_sound, fpZeroC_sound]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    MemRec.zero, MemRec.ext_iff, MemRecExpr.eval_root, MemRecExpr.eval_child,
    MemRecExpr.eval_axis, MemRecExpr.eval_ts]
  tauto

/-! ### The `FP.cons` symbolic expression and the `z·zinv = 1` witness gate -/

/-- The symbolic `cons` on fingerprints, using the `zinv` witness column (93) for `z⁻¹`
    (challenge 1 is `z`).  Polynomial: no division appears. -/
def consExpr (a b : FPExpr) : FPExpr :=
  ⟨ .Mul a.size b.size,
    .Add (.Add (.Mul (chl 1) a.dyck) (.Mul (.Mul a.size a.size) (tc 93)))
         (.Mul (.Mul a.size a.size) b.dyck),
    .Add a.leaf (.Mul a.size b.leaf) ⟩

/-- Evaluated under `computeEnvFull` (where `zinv = z⁻¹`), `consExpr` computes exactly the
    honest `FP.cons`.  This is where the `z⁻¹` witness idiom is discharged. -/
theorem consExpr_eval (a b : FPExpr) :
    (consExpr a b).eval (computeEnvFull inp op pub dec ex)
      = FP.cons inp.z (a.eval (computeEnvFull inp op pub dec ex))
                      (b.eval (computeEnvFull inp op pub dec ex)) := by
  refine FP.ext ?_ ?_ ?_
  · simp only [consExpr, FPExpr.eval, Expr.eval, FP.cons]
  · simp only [consExpr, FPExpr.eval, Expr.eval, FP.cons, eval_chZ, eval_zinv]
  · simp only [consExpr, FPExpr.eval, Expr.eval, FP.cons]

/-- The product-inverse witness gate `z·zinv − 1`. -/
def zZinvExpr : Expr := .Sub (.Mul (chl 1) (tc 93)) (.Const 1)

/-- **`zZinvExpr` faithfulness.**  The `z·zinv = 1` gate holds (at the honest `zinv = z⁻¹`) iff
    `z ≠ 0` — so it forces a genuine inverse and pins `z ≠ 0`.  Same `z ≠ 0`
    claim, and the same pair of cites, as the design note above and `computeAIR_sound` below:
    `1698` fixes `z` as a `rap_inputs` component, `1716` is the paper's own nonzero-size sentence. -/
theorem zZinvExpr_eval :
    zZinvExpr.eval (computeEnvFull inp op pub dec ex) = 0 ↔ inp.z ≠ 0 := by
  simp only [zZinvExpr, Expr.eval, eval_chZ, eval_zinv, Int.cast_one, sub_eq_zero]
  constructor
  · intro h hz; rw [hz, zero_mul] at h; exact zero_ne_one h
  · intro hz; exact mul_inv_cancel₀ hz

/-! ### Block A — formula decomposition;  Block B — memory record 1 (always active) -/

/-- Block A: `pub.f = FP.cons z f_h f_t`. -/
def formulaExprs : List Expr := fpEqC cF (consExpr cFh cFt)

theorem reified_formula_sound :
    (∀ e ∈ formulaExprs, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ pub.f = FP.cons inp.z dec.f_h dec.f_t := by
  rw [formulaExprs, fpEqC_sound]
  simp only [eval_cF, consExpr_eval, eval_cFh, eval_cFt]

/-- Block B target: `mr1 = ⟨pub.f, dec.f_t, 3, ln_prev·α⟩`. -/
def mr1Target : MemRecExpr := ⟨cF, cFt, .Const 3, .Mul (tc 65) (chl 0)⟩

def mr1Exprs : List Expr := memEqC cMr1 mr1Target

theorem reified_mr1_sound :
    (∀ e ∈ mr1Exprs, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ pub.mr1 = ⟨pub.f, dec.f_t, 3, pub.ln_prev * inp.α⟩ := by
  rw [mr1Exprs, memEqC_sound, eval_cMr1]
  simp only [mr1Target, MemRecExpr.eval, eval_cF, eval_cFt, Expr.eval, eval_lnPrev, eval_chAlpha,
    Int.cast_ofNat]

/-! ### Constructor-eval lemmas (fire only on literal `⟨…⟩`, so they never fight the readers) -/

@[simp] theorem FPExpr.eval_mk (s d l : Expr) (env : Env K) :
    (FPExpr.mk s d l).eval env = ⟨s.eval env, d.eval env, l.eval env⟩ := rfl
@[simp] theorem MemRecExpr.eval_mk (r c : FPExpr) (ax ts : Expr) (env : Env K) :
    (MemRecExpr.mk r c ax ts).eval env = ⟨r.eval env, c.eval env, ax.eval env, ts.eval env⟩ := rfl

/-! ### The OP_4 increment and OP_6 branch-selection symbolic fingerprints -/

/-- Symbolic `FP.inc z x = ⟨z, 0, x.leaf + 1⟩`. -/
def incExpr (x : FPExpr) : FPExpr := ⟨chl 1, .Const 0, .Add x.leaf (.Const 1)⟩

theorem incExpr_eval (x : FPExpr) :
    (incExpr x).eval (computeEnvFull inp op pub dec ex)
      = FP.inc inp.z (x.eval (computeEnvFull inp op pub dec ex)) := by
  apply FP.ext <;> simp [incExpr, FP.inc, Expr.eval, eval_chZ]

/-- Symbolic OP_6 branch `(1−sel)·x + sel·y`, componentwise. -/
def fpBranchExpr (sel : Expr) (x y : FPExpr) : FPExpr :=
  ⟨ .Add (.Mul (.Sub (.Const 1) sel) x.size) (.Mul sel y.size),
    .Add (.Mul (.Sub (.Const 1) sel) x.dyck) (.Mul sel y.dyck),
    .Add (.Mul (.Sub (.Const 1) sel) x.leaf) (.Mul sel y.leaf) ⟩

theorem fpBranchExpr_eval (sel : Expr) (x y : FPExpr) (env : Env K) :
    (fpBranchExpr sel x y).eval env
      = FP.add (FP.smul (1 - sel.eval env) (x.eval env)) (FP.smul (sel.eval env) (y.eval env)) := by
  apply FP.ext <;>
    simp only [fpBranchExpr, FP.add, FP.smul, FPExpr.eval_mk, Expr.eval, Int.cast_one,
      FPExpr.eval_size, FPExpr.eval_dyck, FPExpr.eval_leaf]

/-! ### The `ln` recurrence subterms -/

def lnA1 : Expr := .Mul (tc 65) (chl 0)              -- ln_prev · α
def lnA2 : Expr := .Mul (tc 65) (.Pow (chl 0) 2)     -- ln_prev · α²
def lnA3 : Expr := .Mul (tc 65) (.Pow (chl 0) 3)     -- ln_prev · α³

/-! ### The per-opcode memory-record block `memBlk` -/

def memBlkExprs (st : State) : List Expr :=
  match st with
  | .s0 =>
      memEqC cMr2 ⟨cS, cE, cFt.leaf, lnA2⟩
        ++ memZeroC cMr3
        ++ [.Sub (tc 66) lnA2, .Sub cFt.size (chl 1), cFt.dyck]
  | .s1 | .s3 | .s4 | .cons =>
      memZeroC cMr2 ++ memZeroC cMr3 ++ [.Sub (tc 66) lnA1]
  | .s2 | .s5 | .s7 | .s8 =>
      memEqC cMr2 ⟨cFt, cFth, .Const 2, lnA2⟩
        ++ fpEqC (consExpr cFth cFtt) cFt
        ++ memZeroC cMr3
        ++ [.Sub (tc 66) lnA2]
  | .s6 =>
      memEqC cMr2 ⟨cFt, cFth, .Const 2, lnA2⟩
        ++ fpEqC (consExpr cFth cFtt) cFt
        ++ memEqC cMr3 ⟨cFtt, cFtth, .Const 2, lnA3⟩
        ++ fpEqC (consExpr cFtth cFttt) cFtt
        ++ [.Sub (tc 66) lnA3]
  | .s9 =>
      memEqC cMr2 ⟨cFt, cFth, .Const 2, lnA2⟩
        ++ fpEqC (consExpr cFth cFtt) cFt
        ++ memEqC cMr3 ⟨cSf1e, cSf2f, cFth.leaf, lnA3⟩
        ++ [.Sub (tc 66) lnA3]

/-! ### The per-opcode evaluation block `evalR` -/

def evalRExprs (st : State) : List Expr :=
  match st with
  | .s0 =>
      fpZeroC cSf1s ++ fpZeroC cSf1f ++ fpZeroC cSf1e
        ++ fpZeroC cSf2s ++ fpZeroC cSf2f ++ fpZeroC cSf2e
        ++ fpZeroC cSf3s ++ fpZeroC cSf3f ++ fpZeroC cSf3e
  | .s1 =>
      fpEqC cE cFt
        ++ fpZeroC cSf1s ++ fpZeroC cSf1f ++ fpZeroC cSf1e
        ++ fpZeroC cSf2s ++ fpZeroC cSf2f ++ fpZeroC cSf2e
        ++ fpZeroC cSf3s ++ fpZeroC cSf3f ++ fpZeroC cSf3e
  | .s2 =>
      fpEqC cSf1s cS ++ fpEqC cSf1f cFth ++ fpEqC cSf2s cS ++ fpEqC cSf2f cFtt
        ++ fpEqC cSf3s cSf1e ++ fpEqC cSf3f cSf2e ++ fpEqC cE cSf3e
  | .s3 =>
      fpEqC cSf1s cS ++ fpEqC cSf1f cFt
        ++ fpZeroC cSf2s ++ fpZeroC cSf2f ++ fpZeroC cSf2e
        ++ fpZeroC cSf3s ++ fpZeroC cSf3f ++ fpZeroC cSf3e
        ++ [.Sub cE.size (chl 1), cE.dyck,
            .Mul cE.leaf (.Sub (.Const 1) cE.leaf),
            .Mul (tc 92) (.Sub (.Mul (tc 92) (.Sub (chl 1) cSf1e.size)) (.Const 1)),
            .Mul (.Sub (chl 1) cSf1e.size)
                 (.Sub (.Mul (tc 92) (.Sub (chl 1) cSf1e.size)) (.Const 1)),
            .Sub (.Add (.Mul (tc 92) (.Sub (chl 1) cSf1e.size)) cE.leaf) (.Const 1)]
  | .s4 =>
      fpEqC cSf1s cS ++ fpEqC cSf1f cFt
        ++ [.Sub cSf1e.size (chl 1), cSf1e.dyck]
        ++ fpZeroC cSf2s ++ fpZeroC cSf2f ++ fpZeroC cSf2e
        ++ fpZeroC cSf3s ++ fpZeroC cSf3f ++ fpZeroC cSf3e
        ++ fpEqC cE (incExpr cSf1e)
  | .s5 =>
      fpEqC cSf1s cS ++ fpEqC cSf1f cFth ++ fpEqC cSf2s cS ++ fpEqC cSf2f cFtt
        ++ fpZeroC cSf3s ++ fpZeroC cSf3f ++ fpZeroC cSf3e
        ++ [.Sub cE.size (chl 1), cE.dyck,
            .Mul cE.leaf (.Sub (.Const 1) cE.leaf),
            .Mul (.Sub (.Const 1) cE.leaf) (.Sub cSf1e.size cSf2e.size),
            .Mul (.Sub (.Const 1) cE.leaf) (.Sub cSf1e.dyck cSf2e.dyck),
            .Mul (.Sub (.Const 1) cE.leaf) (.Sub cSf1e.leaf cSf2e.leaf),
            .Sub (.Mul (tc 92)
                   (.Add (.Add (.Add (.Mul (chl 2) (.Sub cSf1e.size cSf2e.size))
                                     (.Mul (chl 3) (.Sub cSf1e.dyck cSf2e.dyck)))
                               (.Mul (chl 4) (.Sub cSf1e.leaf cSf2e.leaf)))
                         (.Sub (.Const 1) cE.leaf))) (.Const 1)]
  | .s6 =>
      fpEqC cSf1s cS
        ++ fpEqC cSf1f (fpBranchExpr cSf2e.leaf cFtth cFttt)
        ++ fpEqC cE cSf1e ++ fpEqC cSf2s cS ++ fpEqC cSf2f cFth
        ++ [.Sub cSf2e.size (chl 1), cSf2e.dyck,
            .Mul cSf2e.leaf (.Sub (.Const 1) cSf2e.leaf)]
        ++ fpZeroC cSf3s ++ fpZeroC cSf3f ++ fpZeroC cSf3e
  | .s7 =>
      fpEqC cSf1s cSf2e ++ fpEqC cSf1f cFtt ++ fpEqC cE cSf1e
        ++ fpEqC cSf2s cS ++ fpEqC cSf2f cFth
        ++ fpZeroC cSf3s ++ fpZeroC cSf3f ++ fpZeroC cSf3e
  | .s8 =>
      fpEqC cSf1s (consExpr cSf2e cS) ++ fpEqC cSf1f cFtt ++ fpEqC cE cSf1e
        ++ fpEqC cSf2s cS ++ fpEqC cSf2f cFth
        ++ fpZeroC cSf3s ++ fpZeroC cSf3f ++ fpZeroC cSf3e
        ++ [.Sub (.Mul (.Mul cSf2e.size cS.size) (tc 92)) (.Const 1)]
  | .s9 =>
      fpEqC cSf1s cS ++ fpEqC cSf1f cFtt ++ fpEqC cSf2s cSf1e ++ fpEqC cE cSf2e
        ++ fpZeroC cSf3s ++ fpZeroC cSf3f ++ fpZeroC cSf3e
        -- Nock itself crashes on a cell axis
        -- (`Nock/Reference.lean`, the `| 9 =>` arm matches `.cell (.atom ax) c`, else `none`),
        -- so every terminating honest trace satisfies the pin
        -- (`StrengtheningScope.op9_pin_free_on_atom_axis`), and the `(z,0,⊥)` idiom is the
        -- paper's own at `:1921` (OP4 `sf1_e`), `:1935` (OP0 `f_t`) and `tab:v_mem` `:2142`.
        ++ [.Sub cFth.size (chl 1), cFth.dyck]
  | .cons =>
      fpEqC cSf1s cS ++ fpEqC cSf1f cFh ++ fpEqC cSf2s cS ++ fpEqC cSf2f cFt
        ++ fpEqC cE (consExpr cSf1e cSf2e)
        ++ fpZeroC cSf3s ++ fpZeroC cSf3f ++ fpZeroC cSf3e
        ++ [.Sub (.Mul (.Mul cSf1e.size cSf2e.size) (tc 92)) (.Const 1)]

/-! ### Per-opcode faithfulness (deliverable #3)

  Every reader/challenge eval lemma, the constraint-list soundness gadgets, the `cons`/`inc`/
  branch eval lemmas, and the list/forall plumbing are bundled into the `reify_tac` macro, so
  each per-opcode theorem is a single `reify_tac`.  All are **tight biconditionals**: the deep
  embedding computes the identical polynomial as the `evalR`/`memBlk` gate, so `eval = 0` is
  definitionally equivalent to the Prop-level constraint. -/

/-- The uniform tactic reducing `(∀ e ∈ block, e.eval env = 0)` to the concrete Prop-level
    gate: reader/challenge evals, the `FP`/`MemRec` constraint-list soundness gadgets, the
    `cons`/`inc`/branch eval lemmas, and the list/forall plumbing, in one `simp only`. -/
macro "reify_tac" : tactic =>
  `(tactic| simp only [eval_cS, eval_cF, eval_cE, eval_cSf1s, eval_cSf1f, eval_cSf1e,
      eval_cSf2s, eval_cSf2f, eval_cSf2e, eval_cSf3s, eval_cSf3f, eval_cSf3e, eval_cFh, eval_cFt,
      eval_cFth, eval_cFtt, eval_cFtth, eval_cFttt, eval_cMr1, eval_cMr2, eval_cMr3, eval_op,
      eval_chAlpha, eval_chZ, eval_chA, eval_chB, eval_chC, eval_lnPrev, eval_ln, eval_consInv,
      eval_invGen, eval_zinv, FPExpr.eval_size, FPExpr.eval_dyck, FPExpr.eval_leaf,
      FPExpr.eval_mk, MemRecExpr.eval_mk, fpEqC_sound, fpZeroC_sound, memEqC_sound,
      memZeroC_sound, consExpr_eval, incExpr_eval, fpBranchExpr_eval, evalRExprs, memBlkExprs,
      lnA1, lnA2, lnA3, ComputeTable.sfz1, ComputeTable.sfz2, ComputeTable.sfz3, Expr.eval,
      sub_eq_zero, Int.cast_one, Int.cast_zero, Int.cast_ofNat, List.forall_mem_append,
      List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
      and_assoc])

-- The per-opcode `simp only` lists many lemmas that are unused in individual cases; this is
-- intentional (one uniform tactic), so silence the (style-only) unused-simp-args linter here.
set_option linter.unusedSimpArgs false

theorem evalRExprs_s0_sound :
    (∀ e ∈ evalRExprs .s0, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (sfz1 pub ∧ sfz2 pub ∧ sfz3 pub) := by
  reify_tac

theorem evalRExprs_s1_sound :
    (∀ e ∈ evalRExprs .s1, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.e = dec.f_t ∧ sfz1 pub ∧ sfz2 pub ∧ sfz3 pub) := by
  reify_tac

theorem evalRExprs_s2_sound :
    (∀ e ∈ evalRExprs .s2, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_th ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_tt
          ∧ pub.sf3_s = pub.sf1_e ∧ pub.sf3_f = pub.sf2_e ∧ pub.e = pub.sf3_e) := by
  reify_tac

theorem evalRExprs_s3_sound :
    (∀ e ∈ evalRExprs .s3, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_t ∧ sfz2 pub ∧ sfz3 pub
          ∧ pub.e.size = inp.z ∧ pub.e.dyck = 0
          ∧ pub.e.leaf * (1 - pub.e.leaf) = 0
          ∧ ex.invGen * (ex.invGen * (inp.z - pub.sf1_e.size) - 1) = 0
          ∧ (inp.z - pub.sf1_e.size) * (ex.invGen * (inp.z - pub.sf1_e.size) - 1) = 0
          ∧ ex.invGen * (inp.z - pub.sf1_e.size) + pub.e.leaf = 1) := by
  reify_tac

theorem evalRExprs_s4_sound :
    (∀ e ∈ evalRExprs .s4, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_t ∧ pub.sf1_e.size = inp.z ∧ pub.sf1_e.dyck = 0
          ∧ sfz2 pub ∧ sfz3 pub ∧ pub.e = FP.inc inp.z pub.sf1_e) := by
  reify_tac

theorem evalRExprs_s5_sound :
    (∀ e ∈ evalRExprs .s5, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_th ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_tt
          ∧ sfz3 pub ∧ pub.e.size = inp.z ∧ pub.e.dyck = 0
          ∧ pub.e.leaf * (1 - pub.e.leaf) = 0
          ∧ (1 - pub.e.leaf) * (pub.sf1_e.size - pub.sf2_e.size) = 0
          ∧ (1 - pub.e.leaf) * (pub.sf1_e.dyck - pub.sf2_e.dyck) = 0
          ∧ (1 - pub.e.leaf) * (pub.sf1_e.leaf - pub.sf2_e.leaf) = 0
          ∧ ex.invGen * (inp.a * (pub.sf1_e.size - pub.sf2_e.size)
              + inp.b * (pub.sf1_e.dyck - pub.sf2_e.dyck)
              + inp.c * (pub.sf1_e.leaf - pub.sf2_e.leaf) + (1 - pub.e.leaf)) = 1) := by
  reify_tac

theorem evalRExprs_s6_sound :
    (∀ e ∈ evalRExprs .s6, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.sf1_s = pub.s
          ∧ pub.sf1_f = FP.add (FP.smul (1 - pub.sf2_e.leaf) dec.f_tth)
                               (FP.smul pub.sf2_e.leaf dec.f_ttt)
          ∧ pub.e = pub.sf1_e ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_th
          ∧ pub.sf2_e.size = inp.z ∧ pub.sf2_e.dyck = 0
          ∧ pub.sf2_e.leaf * (1 - pub.sf2_e.leaf) = 0 ∧ sfz3 pub) := by
  reify_tac

theorem evalRExprs_s7_sound :
    (∀ e ∈ evalRExprs .s7, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.sf1_s = pub.sf2_e ∧ pub.sf1_f = dec.f_tt ∧ pub.e = pub.sf1_e
          ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_th ∧ sfz3 pub) := by
  reify_tac

theorem evalRExprs_s8_sound :
    (∀ e ∈ evalRExprs .s8, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.sf1_s = FP.cons inp.z pub.sf2_e pub.s ∧ pub.sf1_f = dec.f_tt ∧ pub.e = pub.sf1_e
          ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_th ∧ sfz3 pub
          ∧ pub.sf2_e.size * pub.s.size * ex.invGen = 1) := by
  reify_tac

theorem evalRExprs_s9_sound :
    (∀ e ∈ evalRExprs .s9, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_tt ∧ pub.sf2_s = pub.sf1_e
          ∧ pub.e = pub.sf2_e ∧ sfz3 pub
          ∧ dec.f_th.size = inp.z ∧ dec.f_th.dyck = 0) := by
  reify_tac

theorem evalRExprs_cons_sound :
    (∀ e ∈ evalRExprs .cons, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_h ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_t
          ∧ pub.e = FP.cons inp.z pub.sf1_e pub.sf2_e ∧ sfz3 pub
          ∧ pub.sf1_e.size * pub.sf2_e.size * ex.invGen = 1) := by
  reify_tac

theorem memBlkExprs_s0_sound :
    (∀ e ∈ memBlkExprs .s0, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.mr2 = ⟨pub.s, pub.e, dec.f_t.leaf, pub.ln_prev * inp.α ^ 2⟩ ∧ pub.mr3 = MemRec.zero
          ∧ pub.ln = pub.ln_prev * inp.α ^ 2 ∧ dec.f_t.size = inp.z ∧ dec.f_t.dyck = 0) := by
  reify_tac

theorem memBlkExprs_s1_sound :
    (∀ e ∈ memBlkExprs .s1, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.mr2 = MemRec.zero ∧ pub.mr3 = MemRec.zero ∧ pub.ln = pub.ln_prev * inp.α) := by
  reify_tac

theorem memBlkExprs_s2_sound :
    (∀ e ∈ memBlkExprs .s2, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.mr2 = ⟨dec.f_t, dec.f_th, 2, pub.ln_prev * inp.α ^ 2⟩
          ∧ FP.cons inp.z dec.f_th dec.f_tt = dec.f_t ∧ pub.mr3 = MemRec.zero
          ∧ pub.ln = pub.ln_prev * inp.α ^ 2) := by
  reify_tac

theorem memBlkExprs_s3_sound :
    (∀ e ∈ memBlkExprs .s3, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.mr2 = MemRec.zero ∧ pub.mr3 = MemRec.zero ∧ pub.ln = pub.ln_prev * inp.α) := by
  reify_tac

theorem memBlkExprs_s4_sound :
    (∀ e ∈ memBlkExprs .s4, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.mr2 = MemRec.zero ∧ pub.mr3 = MemRec.zero ∧ pub.ln = pub.ln_prev * inp.α) := by
  reify_tac

theorem memBlkExprs_s5_sound :
    (∀ e ∈ memBlkExprs .s5, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.mr2 = ⟨dec.f_t, dec.f_th, 2, pub.ln_prev * inp.α ^ 2⟩
          ∧ FP.cons inp.z dec.f_th dec.f_tt = dec.f_t ∧ pub.mr3 = MemRec.zero
          ∧ pub.ln = pub.ln_prev * inp.α ^ 2) := by
  reify_tac

theorem memBlkExprs_s6_sound :
    (∀ e ∈ memBlkExprs .s6, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.mr2 = ⟨dec.f_t, dec.f_th, 2, pub.ln_prev * inp.α ^ 2⟩
          ∧ FP.cons inp.z dec.f_th dec.f_tt = dec.f_t
          ∧ pub.mr3 = ⟨dec.f_tt, dec.f_tth, 2, pub.ln_prev * inp.α ^ 3⟩
          ∧ FP.cons inp.z dec.f_tth dec.f_ttt = dec.f_tt ∧ pub.ln = pub.ln_prev * inp.α ^ 3) := by
  reify_tac

theorem memBlkExprs_s7_sound :
    (∀ e ∈ memBlkExprs .s7, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.mr2 = ⟨dec.f_t, dec.f_th, 2, pub.ln_prev * inp.α ^ 2⟩
          ∧ FP.cons inp.z dec.f_th dec.f_tt = dec.f_t ∧ pub.mr3 = MemRec.zero
          ∧ pub.ln = pub.ln_prev * inp.α ^ 2) := by
  reify_tac

theorem memBlkExprs_s8_sound :
    (∀ e ∈ memBlkExprs .s8, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.mr2 = ⟨dec.f_t, dec.f_th, 2, pub.ln_prev * inp.α ^ 2⟩
          ∧ FP.cons inp.z dec.f_th dec.f_tt = dec.f_t ∧ pub.mr3 = MemRec.zero
          ∧ pub.ln = pub.ln_prev * inp.α ^ 2) := by
  reify_tac

theorem memBlkExprs_s9_sound :
    (∀ e ∈ memBlkExprs .s9, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.mr2 = ⟨dec.f_t, dec.f_th, 2, pub.ln_prev * inp.α ^ 2⟩
          ∧ FP.cons inp.z dec.f_th dec.f_tt = dec.f_t
          ∧ pub.mr3 = ⟨pub.sf1_e, pub.sf2_f, dec.f_th.leaf, pub.ln_prev * inp.α ^ 3⟩
          ∧ pub.ln = pub.ln_prev * inp.α ^ 3) := by
  reify_tac

theorem memBlkExprs_cons_sound :
    (∀ e ∈ memBlkExprs .cons, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (pub.mr2 = MemRec.zero ∧ pub.mr3 = MemRec.zero ∧ pub.ln = pub.ln_prev * inp.α) := by
  reify_tac

/-! ### The State-Variables block SV2–SV6 -/

@[simp] theorem eval_op0 : (tc 0).eval (computeEnvFull inp op pub dec ex) = op .s0 := rfl
@[simp] theorem eval_op1 : (tc 1).eval (computeEnvFull inp op pub dec ex) = op .s1 := rfl
@[simp] theorem eval_op2 : (tc 2).eval (computeEnvFull inp op pub dec ex) = op .s2 := rfl
@[simp] theorem eval_op3 : (tc 3).eval (computeEnvFull inp op pub dec ex) = op .s3 := rfl
@[simp] theorem eval_op4 : (tc 4).eval (computeEnvFull inp op pub dec ex) = op .s4 := rfl
@[simp] theorem eval_op5 : (tc 5).eval (computeEnvFull inp op pub dec ex) = op .s5 := rfl
@[simp] theorem eval_op6 : (tc 6).eval (computeEnvFull inp op pub dec ex) = op .s6 := rfl
@[simp] theorem eval_op7 : (tc 7).eval (computeEnvFull inp op pub dec ex) = op .s7 := rfl
@[simp] theorem eval_op8 : (tc 8).eval (computeEnvFull inp op pub dec ex) = op .s8 := rfl
@[simp] theorem eval_op9 : (tc 9).eval (computeEnvFull inp op pub dec ex) = op .s9 := rfl
@[simp] theorem eval_op10 : (tc 10).eval (computeEnvFull inp op pub dec ex) = op .cons := rfl

/-- All eleven states, for enumerating the selector columns. -/
def allStates : List State := [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .cons]

theorem mem_allStates (j : State) : j ∈ allStates := by cases j <;> simp [allStates]

/-- SV2 booleanity for the selector in column `i` (`op_i·(1−op_i)`), phrased with `tc`. -/
def svBoolExprF (i : ℕ) : Expr := .Mul (tc i) (.Sub (.Const 1) (tc i))

/-- The eleven SV2 booleanity constraints, indexed by opcode. -/
def svBoolExprs : List Expr := allStates.map (fun j => svBoolExprF (opCol j))

/-- SV3 one-hot: `(Σ_{i=0}^{10} op_i) − 1`. -/
def svOneHotExprF : Expr :=
  .Sub (.Add (tc 0) (.Add (tc 1) (.Add (tc 2) (.Add (tc 3) (.Add (tc 4) (.Add (tc 5)
    (.Add (tc 6) (.Add (tc 7) (.Add (tc 8) (.Add (tc 9) (tc 10))))))))))) (.Const 1)

/-- `Σ_{i=0}^{9} op_i` symbolically. -/
def sum09Expr : Expr :=
  .Add (tc 0) (.Add (tc 1) (.Add (tc 2) (.Add (tc 3) (.Add (tc 4) (.Add (tc 5)
    (.Add (tc 6) (.Add (tc 7) (.Add (tc 8) (tc 9)))))))))

/-- `Σ_{i=0}^{9} i·op_i` symbolically. -/
def sumJExpr : Expr :=
  .Add (.Mul (.Const 0) (tc 0)) (.Add (.Mul (.Const 1) (tc 1)) (.Add (.Mul (.Const 2) (tc 2))
    (.Add (.Mul (.Const 3) (tc 3)) (.Add (.Mul (.Const 4) (tc 4)) (.Add (.Mul (.Const 5) (tc 5))
    (.Add (.Mul (.Const 6) (tc 6)) (.Add (.Mul (.Const 7) (tc 7))
    (.Add (.Mul (.Const 8) (tc 8)) (.Mul (.Const 9) (tc 9))))))))))

/-- SV4: `(1−op_cons)·f_h.size − z·Σ_{0..9} op`. -/
def sv4Expr : Expr := .Sub (.Mul (.Sub (.Const 1) (tc 10)) cFh.size) (.Mul (chl 1) sum09Expr)
/-- SV5: `(1−op_cons)·f_h.dyck + op_cons·(1 − f_h.dyck·cons_inv)`. -/
def sv5Expr : Expr :=
  .Add (.Mul (.Sub (.Const 1) (tc 10)) cFh.dyck)
       (.Mul (tc 10) (.Sub (.Const 1) (.Mul cFh.dyck (tc 91))))
/-- SV6: `(1−op_cons)·f_h.leaf − Σ_{0..9} j·op`. -/
def sv6Expr : Expr := .Sub (.Mul (.Sub (.Const 1) (tc 10)) cFh.leaf) sumJExpr

/-- The full State-Variables constraint block (SV2 booleanity, SV3 one-hot, SV4–6 head). -/
def svExprs : List Expr := svBoolExprs ++ [svOneHotExprF, sv4Expr, sv5Expr, sv6Expr]

theorem svBoolExprF_opCol_eval (j : State) :
    (svBoolExprF (opCol j)).eval (computeEnvFull inp op pub dec ex) = op j * (1 - op j) := by
  cases j <;> simp [svBoolExprF, opCol, Expr.eval, Int.cast_one]

theorem svBoolExprs_sound :
    (∀ e ∈ svBoolExprs, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (∀ j : State, op j * (1 - op j) = 0) := by
  simp only [svBoolExprs, List.forall_mem_map]
  constructor
  · intro h j; rw [← svBoolExprF_opCol_eval inp op pub dec ex j]; exact h j (mem_allStates j)
  · intro h j _; rw [svBoolExprF_opCol_eval inp op pub dec ex j]; exact h j

/-- **`reified_sv_sound` (tight biconditional).**  The reflected SV block evaluates to zero
    (at the honest selector `op := opSel pub.state`) iff the Prop-level `SVsat` holds (with
    `cons_inv := ex.consInv`).  SV2 matches exactly; SV3–SV6 match up to `ring`-rearrangement. -/
theorem reified_sv_sound :
    (∀ e ∈ svExprs, e.eval (computeEnvFull inp (opSel pub.state) pub dec ex) = 0)
      ↔ SVsat inp pub dec ex.consInv := by
  rw [svExprs, List.forall_mem_append, svBoolExprs_sound]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
    svOneHotExprF, sv4Expr, sv5Expr, sv6Expr, sum09Expr, sumJExpr, Expr.eval, eval_op0, eval_op1,
    eval_op2, eval_op3, eval_op4, eval_op5, eval_op6, eval_op7, eval_op8, eval_op9, eval_op10,
    eval_cFh, eval_chZ, eval_consInv, FPExpr.eval_size, FPExpr.eval_dyck, FPExpr.eval_leaf,
    Int.cast_one, Int.cast_zero, Int.cast_ofNat, sub_eq_zero, SVsat, sum09, sumJ]
  constructor
  · rintro ⟨hb, h3, h4, h5, h6⟩
    exact ⟨hb, by linear_combination h3, by linear_combination h4, by linear_combination h5,
           by linear_combination h6⟩
  · rintro ⟨hb, h3, h4, h5, h6⟩
    exact ⟨hb, by linear_combination h3, by linear_combination h4, by linear_combination h5,
           by linear_combination h6⟩

/-- **`reified_sv_sound_free` (tight biconditional, FREE selector).**  Identical to
    `reified_sv_sound` but over a genuinely free selector column `op` (not `opSel pub.state`):
    the reflected SV block evaluates to zero iff the free-selector predicate `SVsatFree` holds.
    This is the free-column entry point used by `computeAIR_sound_free`. -/
theorem reified_sv_sound_free :
    (∀ e ∈ svExprs, e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ SVsatFree inp op dec ex.consInv := by
  rw [svExprs, List.forall_mem_append, svBoolExprs_sound]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
    svOneHotExprF, sv4Expr, sv5Expr, sv6Expr, sum09Expr, sumJExpr, Expr.eval, eval_op0, eval_op1,
    eval_op2, eval_op3, eval_op4, eval_op5, eval_op6, eval_op7, eval_op8, eval_op9, eval_op10,
    eval_cFh, eval_chZ, eval_consInv, FPExpr.eval_size, FPExpr.eval_dyck, FPExpr.eval_leaf,
    Int.cast_one, Int.cast_zero, Int.cast_ofNat, sub_eq_zero, SVsatFree, sum09, sumJ]
  constructor
  · rintro ⟨hb, h3, h4, h5, h6⟩
    exact ⟨hb, by linear_combination h3, by linear_combination h4, by linear_combination h5,
           by linear_combination h6⟩
  · rintro ⟨hb, h3, h4, h5, h6⟩
    exact ⟨hb, by linear_combination h3, by linear_combination h4, by linear_combination h5,
           by linear_combination h6⟩

/-! ### Selector gating and the always-on blocks assembled per opcode -/

/-- Gate an opcode-`k` constraint by its one-hot selector: `op_k · e` (the standard way a single
    fixed AIR constraint list encodes per-opcode logic — inactive rows multiply by `op_k = 0`). -/
def gateBy (k : State) (e : Expr) : Expr := .Mul (tc (opCol k)) e

/-- Every per-opcode memory + evaluation constraint, each gated by its selector. -/
def perStateGated : List Expr :=
  allStates.flatMap (fun k => (memBlkExprs k ++ evalRExprs k).map (gateBy k))

theorem gateBy_eval (k : State) (e : Expr) :
    (gateBy k e).eval (computeEnvFull inp op pub dec ex)
      = op k * e.eval (computeEnvFull inp op pub dec ex) := by
  unfold gateBy
  simp only [Expr.eval, eval_op]

/-- **Gating collapse.**  At the honest selector `op := opSel st`, the gated union of all
    opcodes' blocks holds iff the *active* opcode `st`'s (ungated) block holds — every other
    opcode's constraints vanish (multiplied by `op_k = 0`). -/
theorem gated_forall (st : State) :
    (∀ e ∈ perStateGated, e.eval (computeEnvFull inp (opSel st) pub dec ex) = 0)
      ↔ (∀ e ∈ memBlkExprs st ++ evalRExprs st,
            e.eval (computeEnvFull inp (opSel st) pub dec ex) = 0) := by
  have hself : (opSel (K := K) st) st = 1 := by simp [opSel]
  constructor
  · intro h e he
    have hmem : gateBy st e ∈ perStateGated := by
      unfold perStateGated
      apply List.mem_flatMap.mpr
      refine ⟨st, mem_allStates st, ?_⟩
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    have h2 := h _ hmem
    rw [gateBy_eval, hself, one_mul] at h2
    exact h2
  · intro h e
    unfold perStateGated
    intro he
    obtain ⟨k, -, hke⟩ := List.mem_flatMap.mp he
    rw [List.mem_map] at hke
    obtain ⟨e', he', hee⟩ := hke
    rw [← hee, gateBy_eval]
    by_cases hk : k = st
    · subst hk; rw [hself, one_mul]; exact h e' he'
    · rw [show (opSel (K := K) st) k = 0 by simp [opSel, hk], zero_mul]

/-- The active opcode's memory + evaluation blocks together reflect `memBlk ∧ evalR`.  Proven
    by case-splitting on `pub.state` and invoking the per-opcode faithfulness theorems. -/
theorem perState_sound :
    (∀ e ∈ memBlkExprs pub.state ++ evalRExprs pub.state,
        e.eval (computeEnvFull inp op pub dec ex) = 0)
      ↔ (memBlk inp pub dec ∧ evalR inp pub dec ex.invGen) := by
  rw [List.forall_mem_append]
  cases hst : pub.state <;>
    simp only [hst, memBlk, evalR, memBlkExprs_s0_sound, memBlkExprs_s1_sound,
      memBlkExprs_s2_sound, memBlkExprs_s3_sound, memBlkExprs_s4_sound, memBlkExprs_s5_sound,
      memBlkExprs_s6_sound, memBlkExprs_s7_sound, memBlkExprs_s8_sound, memBlkExprs_s9_sound,
      memBlkExprs_cons_sound, evalRExprs_s0_sound, evalRExprs_s1_sound, evalRExprs_s2_sound,
      evalRExprs_s3_sound, evalRExprs_s4_sound, evalRExprs_s5_sound, evalRExprs_s6_sound,
      evalRExprs_s7_sound, evalRExprs_s8_sound, evalRExprs_s9_sound, evalRExprs_cons_sound,
      and_assoc]

/-! ### The assembled AIR and the aggregate soundness bridge (deliverable #4) -/

/-- **`computeAIR`** — the entire per-row compute-table AIR as serializable data: the SV block,
    the formula-decomposition, memory-record 1, the `z·zinv = 1` witness gate, and every
    per-opcode memory + evaluation constraint (selector-gated).  All constraints are row-local
    (cross-row transition constraints are out of scope for this sprint). -/
def computeAIR : AIR where
  numTraceCols  := 94
  numChallenges := 5
  numPublic     := 0
  constraints :=
    (svExprs.map (fun e => ⟨.row, e⟩)) ++
    (formulaExprs.map (fun e => ⟨.row, e⟩)) ++
    (mr1Exprs.map (fun e => ⟨.row, e⟩)) ++
    [⟨.row, zZinvExpr⟩] ++
    (perStateGated.map (fun e => ⟨.row, e⟩))

/-- **`computeAIR_sound` (tight, unconditional) — faithful reflection at the honest witness.**
    Every constraint of `computeAIR` evaluates to zero (at the honest selector `opSel pub.state`
    and honest `zinv = z⁻¹`) **iff** the full per-row compute RAP `RAPcomp` holds *and* `z ≠ 0`.
    Everything else matches `RAPcomp` conjunct-for-conjunct with
    no side condition.

    SCOPE (spec-redteam, Sprint 16): this is *faithful reflection of `RAPcomp` + soundness/
    completeness at the HONEST witness* — the selector columns (trace 0–10) and `zinv` are fixed
    at their honest values.  The strictly stronger *env-level adversarial soundness* ("any
    assignment of all 94 columns — INCLUDING a free adversarial selector — satisfying the 526
    constraints decodes to a valid `RAPcomp` execution") is now mechanized as
    `computeAIR_sound_free` (Sprint 16b), which pins the free selector via
    `ComputeTable.SV_pins_head` and then reduces to THIS theorem.  Use `computeAIR_sound_free` for
    the Plonky3-facing cheating-prover guarantee; this biconditional remains the honest-witness
    ⟺ characterization it composes with. -/
theorem computeAIR_sound :
    (∀ c ∈ computeAIR.constraints,
        c.expr.eval (computeEnvFull inp (opSel pub.state) pub dec ex) = 0)
      ↔ (RAPcomp inp pub dec ex ∧ inp.z ≠ 0) := by
  simp only [computeAIR, List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  rw [reified_sv_sound, reified_formula_sound, reified_mr1_sound, zZinvExpr_eval, gated_forall,
    perState_sound]
  simp only [RAPcomp]
  tauto

/-- **Soundness direction, unconditional.**  If the serialized AIR is satisfied at the honest
    assignment, the compute RAP holds (dropping the free `z ≠ 0` bonus). -/
theorem computeAIR_toRAP
    (h : ∀ c ∈ computeAIR.constraints,
        c.expr.eval (computeEnvFull inp (opSel pub.state) pub dec ex) = 0) :
    RAPcomp inp pub dec ex :=
  ((computeAIR_sound inp pub dec ex).mp h).1

/-- **The exact biconditional to `RAPcomp`, under the `z ≠ 0` well-formedness condition.** -/
theorem computeAIR_iff_RAP (hz : inp.z ≠ 0) :
    (∀ c ∈ computeAIR.constraints,
        c.expr.eval (computeEnvFull inp (opSel pub.state) pub dec ex) = 0)
      ↔ RAPcomp inp pub dec ex := by
  rw [computeAIR_sound]; exact ⟨fun h => h.1, fun h => ⟨h, hz⟩⟩

/-- **End-to-end to the honest verifier.**  Composing with `ComputeTable.equiv_compute`: the AIR
    is satisfiable (over the auxiliary witness columns `ex`) iff the algorithmic verifier `Vcomp`
    accepts and `z ≠ 0`.  Requires the paper's `WF` genericity (for the OP_5/8/11 gate ⇔ honest
    op step; `z ≠ 0` for the `cons` dyck witness). -/
theorem computeAIR_iff_Vcomp (wf : WF inp pub) :
    (∃ ex : Extra K, ∀ c ∈ computeAIR.constraints,
        c.expr.eval (computeEnvFull inp (opSel pub.state) pub dec ex) = 0)
      ↔ (Vcomp inp pub dec ∧ inp.z ≠ 0) := by
  constructor
  · rintro ⟨ex, h⟩
    obtain ⟨hrap, hz⟩ := (computeAIR_sound inp pub dec ex).mp h
    exact ⟨(equiv_compute inp pub dec wf).mp ⟨ex, hrap⟩, hz⟩
  · rintro ⟨hv, hz⟩
    obtain ⟨ex, hrap⟩ := (equiv_compute inp pub dec wf).mpr hv
    exact ⟨ex, (computeAIR_sound inp pub dec ex).mpr ⟨hrap, hz⟩⟩

/-! ### Env-level ADVERSARIAL soundness over free selector columns (deliverable, Sprint 16b) -/

/-- **`computeAIR_sound_free` — env-level adversarial soundness.**

    "Forces the honest selector" formally: the SV gates (`reified_sv_sound_free` →
    `ComputeTable.SV_pins_head`) admit no adversarial one-hot other than the unique `opSel s`
    whose head-shape matches `f_h`; then `computeAIR_sound` (faithful reflection at that honest
    selector) closes the row to `RAPcomp`.  So **no cheating-selector assignment satisfies the
    exported AIR** — the `∃ s` witness is uniquely determined by the free columns.

    Requires `hchar` (characteristic `0` or `> 11`; see `SV_pins_head`'s field-subtlety note) — the
    only genuine hypothesis beyond the constraints; `z ≠ 0` is *derived* (from the `z·zinv = 1`
    witness gate), not assumed.  The `zinv` column is WLOG honest: `z·zinv = 1` pins it to `z⁻¹`
    uniquely, so it carries no adversarial freedom (`zZinvExpr_eval`). -/
theorem computeAIR_sound_free
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (h : ∀ c ∈ computeAIR.constraints,
        c.expr.eval (computeEnvFull inp op pub dec ex) = 0) :
    ∃ s : State, op = opSel s ∧ RAPcomp inp { pub with state := s } dec ex ∧ inp.z ≠ 0 := by
  -- 1. Extract the State-Variables sub-block from the full constraint list.
  have hSV : ∀ e ∈ svExprs, e.eval (computeEnvFull inp op pub dec ex) = 0 := by
    intro e he
    have hmem : (⟨.row, e⟩ : Constraint) ∈ computeAIR.constraints := by
      apply List.mem_append_left; apply List.mem_append_left
      apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    exact h ⟨.row, e⟩ hmem
  -- 2. The SV gates pin the free selector to a unique honest one-hot `opSel s`.
  have hSVsat : SVsatFree inp op dec ex.consInv :=
    (reified_sv_sound_free inp op pub dec ex).mp hSV
  obtain ⟨s, hs, _hhead⟩ := SV_pins_head inp op pub dec ex.consInv hchar hSVsat
  subst hs
  exact ⟨s, rfl, (computeAIR_sound inp { pub with state := s } dec ex).mp h⟩

/-- **Adversarial soundness, forward form.**  Any satisfying assignment of the exported AIR over
    free selector columns decodes to a valid compute-RAP execution — the honest selector is not
    assumed but forced. -/
theorem computeAIR_toRAP_free
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (h : ∀ c ∈ computeAIR.constraints,
        c.expr.eval (computeEnvFull inp op pub dec ex) = 0) :
    ∃ s : State, op = opSel s ∧ RAPcomp inp { pub with state := s } dec ex :=
  let ⟨s, hs, hrap, _⟩ := computeAIR_sound_free inp op pub dec ex hchar h
  ⟨s, hs, hrap⟩

/-! ## 4. The exporter (symbolic, field-free, computable) -/

/-- Serialization tag for each `VarKind`. -/
def VarKind.tag : VarKind → String
  | .traceCur  => "trace"
  | .traceNext => "trace_next"
  | .challenge => "chal"
  | .publicVal => "pub"

/-- S-expression serialization of an expression (backend-neutral, computable). -/
def Expr.toSexp : Expr → String
  | .Var k i => "(" ++ k.tag ++ " " ++ toString i ++ ")"
  | .Const c => toString c
  | .Add a b => "(+ " ++ a.toSexp ++ " " ++ b.toSexp ++ ")"
  | .Sub a b => "(- " ++ a.toSexp ++ " " ++ b.toSexp ++ ")"
  | .Mul a b => "(* " ++ a.toSexp ++ " " ++ b.toSexp ++ ")"
  | .Neg a   => "(neg " ++ a.toSexp ++ ")"
  | .Pow e n => "(^ " ++ e.toSexp ++ " " ++ toString n ++ ")"

/-- Serialization tag for each `ConstraintKind`. -/
def ConstraintKind.tag : ConstraintKind → String
  | .boundary   => "boundary"
  | .transition => "transition"
  | .terminal   => "terminal"
  | .row        => "row"

/-- JSON object for a single constraint: `{kind, degree, expr}`. -/
def Constraint.toJson (c : Constraint) : String :=
  "{\"kind\": \"" ++ c.kind.tag ++ "\", \"degree\": " ++ toString c.expr.degree
    ++ ", \"expr\": \"" ++ c.expr.toSexp ++ "\"}"

/-- JSON envelope for the whole AIR: interface sizes + the constraint list. -/
def AIR.toJson (air : AIR) : String :=
  "{\"numTraceCols\": " ++ toString air.numTraceCols
    ++ ", \"numChallenges\": " ++ toString air.numChallenges
    ++ ", \"numPublic\": " ++ toString air.numPublic
    ++ ", \"maxDegree\": " ++ toString air.maxDegree
    ++ ", \"constraints\": [" ++ String.intercalate ", " (air.constraints.map Constraint.toJson)
    ++ "]}"

/-- Print the exported slice (the artifact a Plonky3 backend consumes). -/
def exportSlice : IO Unit := IO.println (AIR.toJson computeAIR_slice)

#eval exportSlice

/-- Print the exported **complete per-row compute AIR** (the full artifact). -/
def exportComputeAIR : IO Unit := IO.println (AIR.toJson computeAIR)

#eval exportComputeAIR
#eval s!"computeAIR: maxDegree = {computeAIR.maxDegree}, #constraints = {computeAIR.constraints.length}, #traceCols = {computeAIR.numTraceCols}, #challenges = {computeAIR.numChallenges}"

/-! ## 5. The reified / exportable MEMORY-table AIR

  The exact analogue of §3b for the memory table `RAPmem` of `Nock/MemoryTable.lean`.

  The state selector is a **genuinely free** `op : MState → K` from the START (never baked at
  `opSel p.st`); the SV gates force it one-hot and equal to `opSel s` (`MemoryTable.SV_pins`), then
  the honest-witness bridge closes the row — exactly the compute pattern.

  ─────────────────────────────────────────────────────────────────────────────────────────
  MEMORY TRACE-COLUMN LAYOUT (`numTraceCols = 36`).  Each fingerprint occupies three consecutive
  columns `(size, dyck, leaf)`; the memory record occupies eight plus form R `C'` at col 35.

  Challenge columns (`numChallenges = 9`): 0 = z, 1 = β, 2 = γ, 8 = λ.  Public columns (`numPublic = 0`).

  DESIGN NOTES.
  * `lcSt`/`rcSt` are the child states of `x_out^mem`.  Only `p.lcSt = p.st`
    appears in `eqBlk` (read_root/verify_child); `rcSt` is never constrained, so — mirroring the
    compute table's omission of the unconstrained subformula states — only `lcSt` is decoded, as an
    honest one-hot `opSel p.lcSt` (cols 19–22), and `p.lcSt = p.st` is reflected as the equation
    "the active-state slot of that one-hot is `1`" (`opSel p.lcSt read_root = 1`, cols 21/22).
  * `cons` (decompose) contains `z⁻¹` (`Φ₃`), arithmetized with the `zinv` witness column (34) and
    the `z·zinv = 1` gate, exactly as the compute table's `zZinvExpr` (col 93).  This surfaces
    `z ≠ 0` as the single well-formedness side-condition.
  * The LogUp witness `g` (col 33) is a genuinely FREE column: `pole·g = 1` pins `g = pole⁻¹` and
    derives `pole ≠ 0` (no baked witness this time), mirroring `MemoryTable.inter_iff`. -/

section Memory
open MemoryTable

variable (minp : MemoryTable.Inputs K) (mop : MState → K) (mrow : MemoryTable.Pub K) (mg : K)

/-- The environment decoded from a full memory row.  `mop : MState → K` is the free one-hot
    selector; `mg : K` the free LogUp inverse witness (col 33); every other column is read off
    `mrow`/`minp`.  The `zinv` column (34) is instantiated at the honest witness `minp.z⁻¹`, and the
    `lcSt` one-hot at the honest `MemoryTable.opSel mrow.lcSt`. -/
noncomputable def memoryEnvFull : Env K where
  trace := fun i => match i with
    | 0 => mop MState.decompose | 1 => mop MState.halt
    | 2 => mop MState.read_root | 3 => mop MState.verify_child
    | 4 => mrow.pt.noun.size | 5 => mrow.pt.noun.dyck | 6 => mrow.pt.noun.leaf
    | 7 => mrow.pt.indicator | 8 => mrow.pt.counts
    | 9 => mrow.lc.noun.size | 10 => mrow.lc.noun.dyck | 11 => mrow.lc.noun.leaf
    | 12 => mrow.lc.indicator | 13 => mrow.lc.counts
    | 14 => mrow.rc.noun.size | 15 => mrow.rc.noun.dyck | 16 => mrow.rc.noun.leaf
    | 17 => mrow.rc.indicator | 18 => mrow.rc.counts
    | 19 => MemoryTable.opSel mrow.lcSt MState.decompose
    | 20 => MemoryTable.opSel mrow.lcSt MState.halt
    | 21 => MemoryTable.opSel mrow.lcSt MState.read_root
    | 22 => MemoryTable.opSel mrow.lcSt MState.verify_child
    | 23 => mrow.mem.root.size | 24 => mrow.mem.root.dyck | 25 => mrow.mem.root.leaf
    | 26 => mrow.mem.child.size | 27 => mrow.mem.child.dyck | 28 => mrow.mem.child.leaf
    | 29 => mrow.mem.axis | 30 => mrow.mem.ts
    | 31 => mrow.ipre | 32 => mrow.icur | 33 => mg | 34 => minp.z⁻¹
    | 35 => mrow.cprime
    | _ => 0
  traceNext := fun _ => 0
  chal := fun i => match i with
    | 0 => minp.z | 1 => minp.β | 2 => minp.γ | 8 => mrow.lambda | _ => 0
  pub := fun _ => 0

/-! ### Named readers -/

/-- Parent cell fingerprint reader. -/
def mPt : FPExpr := fpCol 4
/-- Left-child cell fingerprint reader. -/
def mLc : FPExpr := fpCol 9
/-- Right-child cell fingerprint reader. -/
def mRc : FPExpr := fpCol 14
/-- Memory-record reader. -/
def mMem : MemRecExpr := mrCol 23

@[simp] theorem eval_mPt : mPt.eval (memoryEnvFull minp mop mrow mg) = mrow.pt.noun := rfl
@[simp] theorem eval_mLc : mLc.eval (memoryEnvFull minp mop mrow mg) = mrow.lc.noun := rfl
@[simp] theorem eval_mRc : mRc.eval (memoryEnvFull minp mop mrow mg) = mrow.rc.noun := rfl
@[simp] theorem eval_mMem : mMem.eval (memoryEnvFull minp mop mrow mg) = mrow.mem := rfl

@[simp] theorem eval_mPtInd : (tc 7).eval (memoryEnvFull minp mop mrow mg) = mrow.pt.indicator := rfl
@[simp] theorem eval_mPtCnt : (tc 8).eval (memoryEnvFull minp mop mrow mg) = mrow.pt.counts := rfl
@[simp] theorem eval_mLcInd : (tc 12).eval (memoryEnvFull minp mop mrow mg) = mrow.lc.indicator := rfl
@[simp] theorem eval_mLcCnt : (tc 13).eval (memoryEnvFull minp mop mrow mg) = mrow.lc.counts := rfl
@[simp] theorem eval_mRcInd : (tc 17).eval (memoryEnvFull minp mop mrow mg) = mrow.rc.indicator := rfl
@[simp] theorem eval_mRcCnt : (tc 18).eval (memoryEnvFull minp mop mrow mg) = mrow.rc.counts := rfl
@[simp] theorem eval_mMemAxis : (tc 29).eval (memoryEnvFull minp mop mrow mg) = mrow.mem.axis := rfl
@[simp] theorem eval_mMemTs : (tc 30).eval (memoryEnvFull minp mop mrow mg) = mrow.mem.ts := rfl
@[simp] theorem eval_mIpre : (tc 31).eval (memoryEnvFull minp mop mrow mg) = mrow.ipre := rfl
@[simp] theorem eval_mIcur : (tc 32).eval (memoryEnvFull minp mop mrow mg) = mrow.icur := rfl
@[simp] theorem eval_mG : (tc 33).eval (memoryEnvFull minp mop mrow mg) = mg := rfl
@[simp] theorem eval_mZinv : (tc 34).eval (memoryEnvFull minp mop mrow mg) = minp.z⁻¹ := rfl
@[simp] theorem eval_mCprime : (tc 35).eval (memoryEnvFull minp mop mrow mg) = mrow.cprime := rfl

@[simp] theorem eval_mZ : (chl 0).eval (memoryEnvFull minp mop mrow mg) = minp.z := rfl
@[simp] theorem eval_mBeta : (chl 1).eval (memoryEnvFull minp mop mrow mg) = minp.β := rfl
@[simp] theorem eval_mGamma : (chl 2).eval (memoryEnvFull minp mop mrow mg) = minp.γ := rfl
@[simp] theorem eval_mLambda : (chl 8).eval (memoryEnvFull minp mop mrow mg) = mrow.lambda := rfl
/-- After `Expr.eval` unfolds `.Var.challenge 8` to `env.chal 8`. -/
@[simp] theorem memoryEnvFull_chal_lambda :
    (memoryEnvFull minp mop mrow mg).chal 8 = mrow.lambda := rfl

@[simp] theorem eval_lcOpRR :
    (tc 21).eval (memoryEnvFull minp mop mrow mg)
      = MemoryTable.opSel mrow.lcSt MState.read_root := rfl
@[simp] theorem eval_lcOpVC :
    (tc 22).eval (memoryEnvFull minp mop mrow mg)
      = MemoryTable.opSel mrow.lcSt MState.verify_child := rfl

@[simp] theorem eval_mop0 :
    (tc 0).eval (memoryEnvFull minp mop mrow mg) = mop MState.decompose := rfl
@[simp] theorem eval_mop1 : (tc 1).eval (memoryEnvFull minp mop mrow mg) = mop MState.halt := rfl
@[simp] theorem eval_mop2 :
    (tc 2).eval (memoryEnvFull minp mop mrow mg) = mop MState.read_root := rfl
@[simp] theorem eval_mop3 :
    (tc 3).eval (memoryEnvFull minp mop mrow mg) = mop MState.verify_child := rfl

/-! ### The `cons` (with `zinv` witness) and the LogUp `pole` symbolic expressions -/

/-- The symbolic `cons` on fingerprints, using the `zinv` witness column (34) for `z⁻¹` (challenge 0
    is `z`).  Polynomial: no division appears. -/
def mconsExpr (a b : FPExpr) : FPExpr :=
  ⟨ .Mul a.size b.size,
    .Add (.Add (.Mul (chl 0) a.dyck) (.Mul (.Mul a.size a.size) (tc 34)))
         (.Mul (.Mul a.size a.size) b.dyck),
    .Add a.leaf (.Mul a.size b.leaf) ⟩

theorem mconsExpr_eval (a b : FPExpr) :
    (mconsExpr a b).eval (memoryEnvFull minp mop mrow mg)
      = FP.cons minp.z (a.eval (memoryEnvFull minp mop mrow mg))
                       (b.eval (memoryEnvFull minp mop mrow mg)) := by
  refine FP.ext ?_ ?_ ?_
  · simp only [mconsExpr, FPExpr.eval, Expr.eval, FP.cons]
  · simp only [mconsExpr, FPExpr.eval, Expr.eval, FP.cons, eval_mZ, eval_mZinv]
  · simp only [mconsExpr, FPExpr.eval, Expr.eval, FP.cons]

/-- The `z·zinv − 1` witness gate. -/
def zZinvExprM : Expr := .Sub (.Mul (chl 0) (tc 34)) (.Const 1)

theorem zZinvExprM_eval :
    zZinvExprM.eval (memoryEnvFull minp mop mrow mg) = 0 ↔ minp.z ≠ 0 := by
  simp only [zZinvExprM, Expr.eval, eval_mZ, eval_mZinv, Int.cast_one, sub_eq_zero]
  constructor
  · intro h hz; rw [hz, zero_mul] at h; exact zero_ne_one h
  · intro hz; exact mul_inv_cancel₀ hz

/-- The record RLC pole `RLC^γ(mem) − β`, symbolically (challenge 1 = β,
    challenge 2 = γ; columns 23–30 the record).  Degree 1 in the trace. -/
def recRLCExpr : Expr :=
  .Add (.Add (.Add (.Add (.Add (.Add (.Add (.Add
    (tc 23) (.Mul (chl 2) (tc 24))) (.Mul (.Pow (chl 2) 2) (tc 25)))
    (.Mul (.Pow (chl 2) 3) (tc 26))) (.Mul (.Pow (chl 2) 4) (tc 27)))
    (.Mul (.Pow (chl 2) 5) (tc 28))) (.Mul (.Pow (chl 2) 6) (tc 29)))
    (.Mul (.Pow (chl 2) 7) (tc 30)))
    (.Mul (.Pow (chl 2) 8) (tc 35))

def poleExpr : Expr := .Sub recRLCExpr (chl 1)

theorem poleExpr_eval :
    poleExpr.eval (memoryEnvFull minp mop mrow mg) = pole minp mrow.mem mrow.cprime := by
  simp only [poleExpr, recRLCExpr, pole, recRLC, Expr.eval, eval_mBeta, eval_mGamma,
    eval_mMemAxis, eval_mMemTs, eval_mCprime,
    show (tc 23).eval (memoryEnvFull minp mop mrow mg) = mrow.mem.root.size from rfl,
    show (tc 24).eval (memoryEnvFull minp mop mrow mg) = mrow.mem.root.dyck from rfl,
    show (tc 25).eval (memoryEnvFull minp mop mrow mg) = mrow.mem.root.leaf from rfl,
    show (tc 26).eval (memoryEnvFull minp mop mrow mg) = mrow.mem.child.size from rfl,
    show (tc 27).eval (memoryEnvFull minp mop mrow mg) = mrow.mem.child.dyck from rfl,
    show (tc 28).eval (memoryEnvFull minp mop mrow mg) = mrow.mem.child.leaf from rfl]

/-! ### The reflected equality block `eqBlk` and LogUp `intermediate` block, per state -/

/-- The per-state `eqBlk` constraints. -/
noncomputable def memEqBlkExprs (st : MState) : List Expr :=
  match st with
  | .decompose =>
      fpEqC mPt (mconsExpr mLc mRc)
        ++ [.Sub (tc 7) (.Mul (chl 8) (.Add (tc 12) (tc 17))),
            .Sub (tc 8) (.Add (.Add (.Add (tc 13) (tc 18))
              (.Mul (.Sub (chl 8) (.Const 1)) (.Add (tc 12) (tc 17)))) (tc 17))]
        ++ memZeroC mMem
  | .halt =>
      [.Sub mPt.size (chl 0), mPt.dyck, tc 7, tc 8]
        ++ (fpZeroC mLc ++ [tc 12, tc 13])
        ++ (fpZeroC mRc ++ [tc 17, tc 18])
        ++ memZeroC mMem
  | .read_root =>
      fpEqC mPt mLc
        ++ [.Sub (tc 21) (.Const 1),
            .Sub (tc 7) (.Sub (tc 12)
              (.Mul (.Mul (.Pow (chl 8) (MemoryTable.pwScaleExp K)) (tc 29)) (tc 30))),
            .Sub (tc 8) (.Sub (tc 13)
              (.Mul (.Mul (tc 29) (tc 35)) (tc 30)))]
        ++ fpEqC mMem.root mPt
        ++ (fpZeroC mRc ++ [tc 17, tc 18])
  | .verify_child =>
      fpEqC mPt mLc
        ++ [.Sub (tc 22) (.Const 1),
            .Sub (tc 7) (.Add (tc 12)
              (.Mul (.Pow (chl 8) (MemoryTable.pwScaleExp K)) (tc 30))),
            .Sub (tc 8) (.Add (tc 13)
              (.Mul (.Pow (chl 8) (MemoryTable.pwScaleExp K)) (tc 30)))]
        ++ fpEqC mMem.child mPt
        ++ (fpZeroC mRc ++ [tc 17, tc 18])

/-- The per-state LogUp `intermediate` constraints, over the free witness column `g` (col 33).  `read_root`/`verify_child` use the product-inverse gate
    `pole·g = 1` plus `Δ = ±g`; `decompose`/`halt` leave the accumulator unchanged (`icur = ipre`). -/
def memInterExprs (st : MState) : List Expr :=
  match st with
  | .decompose | .halt => [.Sub (tc 32) (tc 31)]
  | .read_root =>
      [.Sub (.Mul poleExpr (tc 33)) (.Const 1),
       .Sub (.Sub (tc 32) (tc 31)) (tc 33)]
  | .verify_child =>
      [.Sub (.Mul poleExpr (tc 33)) (.Const 1),
       .Add (.Sub (tc 32) (tc 31)) (tc 33)]

/-! ### Per-state faithfulness (tight biconditionals) -/

/-- Uniform tactic reducing `(∀ e ∈ block, e.eval env = 0)` to the concrete `MemoryTable` gate. -/
macro "mreify_tac" : tactic =>
  `(tactic| simp only [eval_mPt, eval_mLc, eval_mRc, eval_mMem, eval_mPtInd, eval_mPtCnt,
      eval_mLcInd, eval_mLcCnt, eval_mRcInd, eval_mRcCnt, eval_mMemAxis, eval_mMemTs, eval_mIpre,
      eval_mIcur, eval_mG, eval_mZinv, eval_mCprime, eval_mZ, eval_mBeta, eval_mGamma, eval_mLambda,
      memoryEnvFull_chal_lambda, eval_lcOpRR, eval_lcOpVC,
      FPExpr.eval_size, FPExpr.eval_dyck, FPExpr.eval_leaf, FPExpr.eval_mk, MemRecExpr.eval_mk,
      MemRecExpr.eval_root, MemRecExpr.eval_child, MemRecExpr.eval_axis, MemRecExpr.eval_ts,
      fpEqC_sound, fpZeroC_sound, memZeroC_sound, mconsExpr_eval, poleExpr_eval,
      memEqBlkExprs, memInterExprs,
      MemoryTable.Cell.zero_iff, MemoryTable.opSel_read_root_eq_one_iff,
      MemoryTable.opSel_verify_child_eq_one_iff, Expr.eval, sub_eq_zero, add_eq_zero_iff_eq_neg,
      Int.cast_one, Int.cast_zero,
      Int.cast_two, Int.cast_ofNat, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true, and_assoc] <;> tauto)

set_option linter.unusedSimpArgs false

theorem memEqBlkExprs_decompose_sound :
    (∀ e ∈ memEqBlkExprs (K := K) MState.decompose, e.eval (memoryEnvFull minp mop mrow mg) = 0)
      ↔ (mrow.pt.noun = FP.cons minp.z mrow.lc.noun mrow.rc.noun
          ∧ mrow.pt.indicator = mrow.lambda * (mrow.lc.indicator + mrow.rc.indicator)
          ∧ mrow.pt.counts = mrow.lc.counts + mrow.rc.counts
              + (mrow.lambda - 1) * (mrow.lc.indicator + mrow.rc.indicator) + mrow.rc.indicator
          ∧ mrow.mem = MemRec.zero) := by
  mreify_tac
  try simp [and_assoc]

theorem memEqBlkExprs_halt_sound :
    (∀ e ∈ memEqBlkExprs (K := K) MState.halt, e.eval (memoryEnvFull minp mop mrow mg) = 0)
      ↔ (mrow.pt.noun.size = minp.z ∧ mrow.pt.noun.dyck = 0
          ∧ mrow.pt.indicator = 0 ∧ mrow.pt.counts = 0
          ∧ mrow.lc = Cell.zero ∧ mrow.rc = Cell.zero
          ∧ mrow.mem = MemRec.zero) := by
  mreify_tac
  try simp [and_assoc]

theorem memEqBlkExprs_read_root_sound :
    (∀ e ∈ memEqBlkExprs (K := K) MState.read_root, e.eval (memoryEnvFull minp mop mrow mg) = 0)
      ↔ (mrow.pt.noun = mrow.lc.noun ∧ mrow.lcSt = MState.read_root
          ∧ mrow.pt.indicator =
              mrow.lc.indicator -
                mrow.lambda ^ MemoryTable.pwScaleExp K * mrow.mem.axis * mrow.mem.ts
          ∧ mrow.pt.counts =
              mrow.lc.counts - mrow.mem.axis * mrow.cprime * mrow.mem.ts
          ∧ mrow.mem.root = mrow.pt.noun
          ∧ mrow.rc = Cell.zero) := by
  mreify_tac
  try simp [and_assoc]

theorem memEqBlkExprs_verify_child_sound :
    (∀ e ∈ memEqBlkExprs (K := K) MState.verify_child, e.eval (memoryEnvFull minp mop mrow mg) = 0)
      ↔ (mrow.pt.noun = mrow.lc.noun ∧ mrow.lcSt = MState.verify_child
          ∧ mrow.pt.indicator =
              mrow.lc.indicator + mrow.lambda ^ MemoryTable.pwScaleExp K * mrow.mem.ts
          ∧ mrow.pt.counts =
              mrow.lc.counts + mrow.lambda ^ MemoryTable.pwScaleExp K * mrow.mem.ts
          ∧ mrow.mem.child = mrow.pt.noun
          ∧ mrow.rc = Cell.zero) := by
  mreify_tac
  try simp [and_assoc]

theorem memInterExprs_decompose_sound :
    (∀ e ∈ memInterExprs MState.decompose, e.eval (memoryEnvFull minp mop mrow mg) = 0)
      ↔ mrow.icur = mrow.ipre := by
  mreify_tac
  try simp [and_assoc]

theorem memInterExprs_halt_sound :
    (∀ e ∈ memInterExprs MState.halt, e.eval (memoryEnvFull minp mop mrow mg) = 0)
      ↔ mrow.icur = mrow.ipre := by
  mreify_tac
  try simp [and_assoc]

theorem memInterExprs_read_root_sound :
    (∀ e ∈ memInterExprs MState.read_root, e.eval (memoryEnvFull minp mop mrow mg) = 0)
      ↔ (pole minp mrow.mem mrow.cprime * mg = 1 ∧ mrow.icur - mrow.ipre = mg) := by
  mreify_tac
  try simp [and_assoc]

theorem memInterExprs_verify_child_sound :
    (∀ e ∈ memInterExprs MState.verify_child, e.eval (memoryEnvFull minp mop mrow mg) = 0)
      ↔ (pole minp mrow.mem mrow.cprime * mg = 1 ∧ mrow.icur - mrow.ipre = -mg) := by
  mreify_tac
  try simp [and_assoc]

/-- **`mem_perState_sound`.**  The active state's `eqBlk` + `intermediate` blocks together reflect
    `eqBlk ∧ interR`.  Proven by case-splitting on `mrow.st` and the per-state faithfulness. -/
theorem mem_perState_sound :
    (∀ e ∈ memEqBlkExprs (K := K) mrow.st ++ memInterExprs mrow.st,
        e.eval (memoryEnvFull minp mop mrow mg) = 0)
      ↔ (eqBlk minp mrow ∧ interR minp mrow mg) := by
  rw [List.forall_mem_append]
  cases hst : mrow.st <;>
    simp only [hst, eqBlk, interR, memEqBlkExprs_decompose_sound, memEqBlkExprs_halt_sound,
      memEqBlkExprs_read_root_sound, memEqBlkExprs_verify_child_sound,
      memInterExprs_decompose_sound, memInterExprs_halt_sound, memInterExprs_read_root_sound,
      memInterExprs_verify_child_sound, and_assoc]

/-! ### The State-Variables block and selector gating -/

def mopCol : MState → ℕ
  | .decompose => 0 | .halt => 1 | .read_root => 2 | .verify_child => 3

def allMStates : List MState := [.decompose, .halt, .read_root, .verify_child]

theorem mem_allMStates (j : MState) : j ∈ allMStates := by cases j <;> simp [allMStates]

/-- SV booleanity for the selector in column `i`: `op_i·(1−op_i)`. -/
def memSvBoolExprF (i : ℕ) : Expr := .Mul (tc i) (.Sub (.Const 1) (tc i))

def memSvBoolExprs : List Expr := allMStates.map (fun j => memSvBoolExprF (mopCol j))

/-- SV one-hot: `(Σ_{i=0}^{3} op_i) − 1`. -/
def memSvOneHotExpr : Expr :=
  .Sub (.Add (tc 0) (.Add (tc 1) (.Add (tc 2) (tc 3)))) (.Const 1)

def memSvExprs : List Expr := memSvBoolExprs ++ [memSvOneHotExpr]

theorem memSvBoolExprF_eval (j : MState) :
    (memSvBoolExprF (mopCol j)).eval (memoryEnvFull minp mop mrow mg) = mop j * (1 - mop j) := by
  cases j <;> simp [memSvBoolExprF, mopCol, Expr.eval, Int.cast_one]

theorem memSvBoolExprs_sound :
    (∀ e ∈ memSvBoolExprs, e.eval (memoryEnvFull minp mop mrow mg) = 0)
      ↔ (∀ j : MState, mop j * (1 - mop j) = 0) := by
  simp only [memSvBoolExprs, List.forall_mem_map]
  constructor
  · intro h j; rw [← memSvBoolExprF_eval minp mop mrow mg j]; exact h j (mem_allMStates j)
  · intro h j _; rw [memSvBoolExprF_eval minp mop mrow mg j]; exact h j

/-- **`reified_mem_sv_sound_free` (tight biconditional, FREE selector).**  The reflected SV block
    evaluates to zero iff the free-selector predicate `SVsatFree` holds. -/
theorem reified_mem_sv_sound_free :
    (∀ e ∈ memSvExprs, e.eval (memoryEnvFull minp mop mrow mg) = 0)
      ↔ MemoryTable.SVsatFree mop := by
  rw [memSvExprs, List.forall_mem_append, memSvBoolExprs_sound]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
    memSvOneHotExpr, Expr.eval, eval_mop0, eval_mop1, eval_mop2, eval_mop3, Int.cast_one,
    sub_eq_zero, MemoryTable.SVsatFree, sum4]
  constructor
  · rintro ⟨hb, h⟩; exact ⟨hb, by linear_combination h⟩
  · rintro ⟨hb, h⟩; exact ⟨hb, by linear_combination h⟩

/-- Gate an opcode-`k` constraint by its one-hot selector: `op_k · e`. -/
def gateByM (k : MState) (e : Expr) : Expr := .Mul (tc (mopCol k)) e

/-- Every per-state `eqBlk` + `intermediate` constraint, gated by its selector. -/
noncomputable def memPerStateGated : List Expr :=
  allMStates.flatMap (fun k => (memEqBlkExprs (K := K) k ++ memInterExprs k).map (gateByM k))

theorem gateByM_eval (k : MState) (e : Expr) :
    (gateByM k e).eval (memoryEnvFull minp mop mrow mg)
      = mop k * e.eval (memoryEnvFull minp mop mrow mg) := by
  unfold gateByM; cases k <;> simp only [Expr.eval, mopCol, eval_mop0, eval_mop1, eval_mop2,
    eval_mop3]

/-- **Gating collapse.**  At the honest selector `mop := opSel st`, the gated union of all states'
    blocks holds iff the active state `st`'s (ungated) block holds. -/
theorem mem_gated_forall (st : MState) :
    (∀ e ∈ memPerStateGated (K := K), e.eval (memoryEnvFull minp (MemoryTable.opSel st) mrow mg) = 0)
      ↔ (∀ e ∈ memEqBlkExprs (K := K) st ++ memInterExprs st,
            e.eval (memoryEnvFull minp (MemoryTable.opSel st) mrow mg) = 0) := by
  have hself : (MemoryTable.opSel (K := K) st) st = 1 := by simp [MemoryTable.opSel]
  constructor
  · intro h e he
    have hmem : gateByM st e ∈ memPerStateGated (K := K) := by
      unfold memPerStateGated
      apply List.mem_flatMap.mpr
      refine ⟨st, mem_allMStates st, ?_⟩
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    have h2 := h _ hmem
    rw [gateByM_eval, hself, one_mul] at h2
    exact h2
  · intro h e
    unfold memPerStateGated
    intro he
    obtain ⟨k, -, hke⟩ := List.mem_flatMap.mp he
    rw [List.mem_map] at hke
    obtain ⟨e', he', hee⟩ := hke
    rw [← hee, gateByM_eval]
    by_cases hk : k = st
    · subst hk; rw [hself, one_mul]; exact h e' he'
    · rw [show (MemoryTable.opSel (K := K) st) k = 0 by simp [MemoryTable.opSel, hk], zero_mul]

/-! ### The assembled memory AIR and the soundness bridges -/

/-- **`(memoryAIR (K := K))`** — the entire per-row memory-table AIR as serializable data: the SV block, the
    `z·zinv = 1` witness gate, and every per-state equality + LogUp `intermediate` constraint
    (selector-gated).  All constraints are row-local (the cross-row transition constraints —
    `icur[i] = ipre[i+1]`, the Walk/IO recurrences — are out of scope for this sprint). -/
noncomputable def memoryAIR : AIR where
  numTraceCols  := 36
  numChallenges := 9
  numPublic     := 0
  constraints :=
    (memSvExprs.map (fun e => ⟨.row, e⟩)) ++
    [⟨.row, zZinvExprM⟩] ++
    ((memPerStateGated (K := K)).map (fun e => ⟨.row, e⟩))

/-- **`memoryAIR_sound` (tight) — faithful reflection at the honest witness.**  Every constraint of
    `(memoryAIR (K := K))` evaluates to zero (at the honest selector `opSel mrow.st` and the free witness `mg`)
    **iff** the full per-row memory RAP `RAPmem` holds *and* `z ≠ 0`.  The `z ≠ 0` conjunct is
    contributed solely by the `z·zinv = 1` witness gate (`zZinvExprM`); it corresponds to no
    `RAPmem` constraint and reflects the paper's random-input genericity. -/
theorem memoryAIR_sound :
    (∀ c ∈ (memoryAIR (K := K)).constraints,
        c.expr.eval (memoryEnvFull minp (MemoryTable.opSel mrow.st) mrow mg) = 0)
      ↔ (RAPmem minp mrow mg ∧ minp.z ≠ 0) := by
  simp only [memoryAIR, List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  rw [reified_mem_sv_sound_free, zZinvExprM_eval, mem_gated_forall, mem_perState_sound]
  rw [← MemoryTable.SVsat_eq_free]
  simp only [RAPmem]
  tauto

/-- **Soundness direction, unconditional.**  Honest satisfaction of the serialized AIR implies the
    memory RAP (dropping the free `z ≠ 0` bonus). -/
theorem memoryAIR_toRAP
    (h : ∀ c ∈ (memoryAIR (K := K)).constraints,
        c.expr.eval (memoryEnvFull minp (MemoryTable.opSel mrow.st) mrow mg) = 0) :
    RAPmem minp mrow mg :=
  ((memoryAIR_sound minp mrow mg).mp h).1

/-- **End-to-end to the algorithmic verifier.**  Composing with `MemoryTable.equiv_mem`: the AIR is
    satisfiable (over the free LogUp witness `g`) iff `V_mem` accepts and `z ≠ 0`.  Requires the
    paper's `WF` genericity (`pole ≠ 0` in the two record-touching states). -/
theorem memoryAIR_iff_Vmem (wf : MemoryTable.WF minp mrow) :
    (∃ g : K, ∀ c ∈ (memoryAIR (K := K)).constraints,
        c.expr.eval (memoryEnvFull minp (MemoryTable.opSel mrow.st) mrow g) = 0)
      ↔ (Vmem minp mrow ∧ minp.z ≠ 0) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨g, hg⟩
    obtain ⟨hrap, hz⟩ := (memoryAIR_sound minp mrow g).mp hg
    exact ⟨(equiv_mem minp mrow wf).mp ⟨g, hrap⟩, hz⟩
  · rintro ⟨hv, hz⟩
    obtain ⟨g, hrap⟩ := (equiv_mem minp mrow wf).mpr hv
    exact ⟨g, (memoryAIR_sound minp mrow g).mpr ⟨hrap, hz⟩⟩

/-- **`memoryAIR_sound_free` — env-level ADVERSARIAL soundness.**  The cheating-prover guarantee:
    over a *genuinely free* selector valuation `mop : MState → K` (the four one-hot columns 0–3, NOT
    fixed at `opSel mrow.st`) AND a *genuinely free* LogUp witness column `mg` (col 33, no baked
    inverse), any assignment satisfying every `(memoryAIR (K := K))` constraint is FORCED onto the honest
    track: the selector is one-hot, `mop = opSel s`, and the row is a genuine memory-RAP execution
    for that state `s`.

    "Forces the honest selector" formally: the SV gates (`reified_mem_sv_sound_free` →
    `MemoryTable.SV_pins`) admit no adversarial one-hot other than a unique `opSel s`; then
    `memoryAIR_sound` closes the row.  So **no cheating-selector assignment satisfies the exported
    memory AIR** — the `∃ s` witness is uniquely determined by the free columns.

    The only
    genuine hypothesis beyond the constraints is `hchar` (characteristic `0` or `> 4`). -/
theorem memoryAIR_sound_free
    (hchar : ∀ n : ℕ, n ≤ 4 → (n : K) = 1 → n = 1)
    (h : ∀ c ∈ (memoryAIR (K := K)).constraints,
        c.expr.eval (memoryEnvFull minp mop mrow mg) = 0) :
    ∃ s : MState, mop = MemoryTable.opSel s
        ∧ RAPmem minp { mrow with st := s } mg ∧ minp.z ≠ 0 := by
  -- 1. Extract the State-Variables sub-block.
  have hSV : ∀ e ∈ memSvExprs, e.eval (memoryEnvFull minp mop mrow mg) = 0 := by
    intro e he
    have hmem : (⟨.row, e⟩ : Constraint) ∈ (memoryAIR (K := K)).constraints := by
      apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    exact h ⟨.row, e⟩ hmem
  -- 2. The SV gates pin the free selector to a unique honest one-hot `opSel s`.
  have hSVsat : MemoryTable.SVsatFree mop := (reified_mem_sv_sound_free minp mop mrow mg).mp hSV
  obtain ⟨s, hs⟩ := MemoryTable.SV_pins mop hchar hSVsat
  subst hs
  exact ⟨s, rfl, (memoryAIR_sound minp { mrow with st := s } mg).mp h⟩

/-- **Adversarial soundness, forward form.**  Any satisfying assignment of the exported memory AIR
    over free selector + LogUp witness columns decodes to a valid memory-RAP execution — the honest
    selector is not assumed but forced. -/
theorem memoryAIR_toRAP_free
    (hchar : ∀ n : ℕ, n ≤ 4 → (n : K) = 1 → n = 1)
    (h : ∀ c ∈ (memoryAIR (K := K)).constraints,
        c.expr.eval (memoryEnvFull minp mop mrow mg) = 0) :
    ∃ s : MState, mop = MemoryTable.opSel s ∧ RAPmem minp { mrow with st := s } mg :=
  let ⟨s, hs, hrap, _⟩ := memoryAIR_sound_free minp mop mrow mg hchar h
  ⟨s, hs, hrap⟩

/-! ### Degree accounting and export -/

def exprMax (es : List Expr) : ℕ :=
  es.foldr (fun e acc => max e.degree acc) 0

theorem exprMax_append (a b : List Expr) :
    exprMax (a ++ b) = max (exprMax a) (exprMax b) := by
  induction a with
  | nil => simp [exprMax]
  | cons x xs ih =>
    simp only [exprMax] at ih
    simp only [List.cons_append, exprMax, List.foldr_cons]
    rw [ih, ← Nat.max_assoc]

theorem exprMax_map_mulTrace (i : ℕ) (es : List Expr) :
    exprMax (es.map (fun e => .Mul (.Var .traceCur i) e)) =
      es.foldr (fun e acc => max (1 + e.degree) acc) 0 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [exprMax] at ih
    simp only [List.map_cons, exprMax, List.foldr_cons, Expr.degree]
    rw [ih]

theorem exprMax_gateByM (k : MState) (es : List Expr) :
    exprMax (es.map (gateByM k)) =
      es.foldr (fun e acc => max (1 + e.degree) acc) 0 := by
  unfold gateByM tc
  exact exprMax_map_mulTrace (mopCol k) es

def constraintMax (cs : List Constraint) : ℕ :=
  cs.foldr (fun c acc => max c.expr.degree acc) 0

theorem constraintMax_append (a b : List Constraint) :
    constraintMax (a ++ b) = max (constraintMax a) (constraintMax b) := by
  induction a with
  | nil => simp [constraintMax]
  | cons x xs ih =>
    simp only [constraintMax] at ih
    simp only [List.cons_append, constraintMax, List.foldr_cons]
    rw [ih, ← Nat.max_assoc]

theorem constraintMax_row (es : List Expr) :
    constraintMax (es.map (fun e => (⟨.row, e⟩ : Constraint))) = exprMax es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [exprMax, constraintMax] at ih
    simp only [List.map_cons, constraintMax, exprMax, List.foldr_cons]
    rw [ih]

set_option maxHeartbeats 800000 in
theorem mem_slice_maxDegree : (memoryAIR (K := K)).maxDegree = 4 := by
  have hper : exprMax (memPerStateGated (K := K)) = 4 := by
    simp only [memPerStateGated, allMStates, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [exprMax_append, exprMax_append, exprMax_append]
    rw [exprMax_gateByM, exprMax_gateByM, exprMax_gateByM, exprMax_gateByM]
    rfl
  change constraintMax (memoryAIR (K := K)).constraints = 4
  simp only [memoryAIR]
  rw [constraintMax_append, constraintMax_append, constraintMax_row, constraintMax_row]
  have hz : constraintMax [⟨.row, zZinvExprM⟩] = 1 := by
    unfold constraintMax zZinvExprM chl tc Expr.degree
    rfl
  have hsv : exprMax memSvExprs = 2 := by rfl
  rw [hz, hsv, hper]
  rfl

/-- Print the exported **complete per-row memory AIR** (the full artifact). -/
noncomputable def exportMemoryAIR : IO Unit := IO.println (AIR.toJson (memoryAIR (K := K)))

-- `(memoryAIR (K := K))` carries `Nat.size (ringChar K)`, so the exporter does not reduce.

end Memory

/-! ## 6. Cross-row TRANSITION constraints — activating `traceNext` (Tier A)

  Everything above (`computeAIR`/`(memoryAIR (K := K))`, the `*_sound_free` bridges) is **row-local**: each
  constraint is a `.row` gate, `traceNext` is inert (`fun _ => 0`), so the export proves every row
  valid but NOT that the rows form a coherent execution.  This section makes the machine
  *end-to-end* by REIFYING the already-proven cross-row recurrences as genuine `.transition`
  (and `.boundary`/`.terminal`) constraints that really read the next row.

  ─────────────────────────────────────────────────────────────────────────────────────────
  How `traceNext` is activated: the TWO-ROW environment.
  ─────────────────────────────────────────────────────────────────────────────────────────
  A transition gate spans two adjacent rows `i, i+1`.  `twoRow cur next` glues two single-row
  `Env`s: `.trace` reads the *current* row `cur`, `.traceNext` reads the *next* row `next`
  (challenges/publics are shared).  So `.Var.traceCur j` reads column `j` of row `i`, and
  `.Var.traceNext j` (`tn j`) reads column `j` of row `i+1` — exactly Plonky3's `main.local`
  vs `main.next`.  This is the mechanism the docstring's `VarKind.traceNext` always promised;
  it was `fun _ => 0` until now.

  What is reified (all recurrences are ALREADY PROVEN; we express them as gates + prove
  `gate.eval = 0 ↔ proven step predicate`):
    * **Walk α-telescoping** (`Walk.WalkSat`): `ln(i+1)=α·ln(i)`, `count(i+1)=count(i)·α^fanout`,
      the multiset accumulation step, plus the `.boundary` init (`ln(1)=α`, `count(1)`, `accInit`)
      and the `.terminal` `out_walk = acc(h) = 0`.  Reconstructs `WalkSat` verbatim.
    * **Memory LogUp chaining**: `ipre(0)=0` at `.boundary`,
      `icur(i) = ipre(i+1)` at `.transition`, and `icur(last)=0` at `.terminal`, over the real
      `(memoryAIR (K := K))` columns (31 = ipre, 32 = icur).  Together these close both endpoints and the
      cross-row hand-off of the global LogUp accumulator.
    * **IO accumulators** (`IO.ProgIOSat`/`IO.MemIOSat`): `acc(i+1)=acc(i)±frac`, `.boundary`
      init, `.terminal` output checks.  Reconstructs the extended RAP accumulators of `Thm:IO_result`.

  NOTE (research item, NOT this sprint): the `z^i` axis-batching SOUNDNESS
  is separate.  We supply the transition SUBSTRATE the batching will run over (the committed
  child-sum / frac columns), but do not prove its soundness here. -/

namespace Trans

open Classical

/-! ### The two-row environment (the `traceNext` activation) -/

variable {K : Type*} [Field K]

-- The structural `twoRow_*` readers hold by `rfl` and do not use `[Field K]`; silence the
-- (style-only) unused-section-variable linter for the namespace (matching the file's posture).
set_option linter.unusedSectionVars false

/-- **The two-row environment.**  `.trace` reads the current row `cur`, `.traceNext` reads the
    next row `next`; challenges/publics are the current row's.  A `.transition` `Expr` therefore
    reads row `i` via `.Var.traceCur _` and row `i+1` via `.Var.traceNext _`. -/
def twoRow (cur next : Env K) : Env K where
  trace     := cur.trace
  traceNext := next.trace
  chal      := cur.chal
  pub       := cur.pub

/-- Next-row column reader (`main.next`). -/
def tn (i : ℕ) : Expr := .Var .traceNext i
/-- Public-value reader. -/
def pubv (i : ℕ) : Expr := .Var .publicVal i

@[simp] theorem twoRow_trace (cur next : Env K) (i : ℕ) :
    (twoRow cur next).trace i = cur.trace i := rfl
@[simp] theorem twoRow_traceNext (cur next : Env K) (i : ℕ) :
    (twoRow cur next).traceNext i = next.trace i := rfl
@[simp] theorem twoRow_chal (cur next : Env K) (i : ℕ) :
    (twoRow cur next).chal i = cur.chal i := rfl
@[simp] theorem twoRow_pub (cur next : Env K) (i : ℕ) :
    (twoRow cur next).pub i = cur.pub i := rfl

/-! ### Memory LogUp endpoint gates and chaining (resolves the memory-AIR LOW caveat)

  The memory table's LogUp accumulator `W_mem` starts at zero, is handed from one row to the next,
  and ends at zero.  Thus `ipre` (`intermediate_i`, column 31) is zero on the first row; `icur`
  (`intermediate_{i+1}`, column 32) of row `i` equals `ipre` of row `i+1`; and `icur` is zero on the
  last row.  `(memoryAIR (K := K))` alone leaves these endpoint and cross-row facts UNCONSTRAINED (the per-row
  `interR` only ties `icur − ipre` to `±g` *within* a row). -/

section MemChain
open MemoryTable Reified

/-- **Memory chaining gate** `icur(i) − ipre(i+1)` (transition; degree 1). -/
def icurChainExpr : Expr := .Sub (Reified.tc 32) (tn 31)

/-- **Memory LogUp initial-value gate** `ipre(0)` (boundary; column 31; degree 1). -/
def memIpreInitExpr : Expr := Reified.tc 31

/-- **Memory LogUp terminal-value gate** `icur(last)` (terminal; column 32; degree 1). -/
def memIcurTermExpr : Expr := Reified.tc 32

/-- **`reified_icur_chain_sound` (tight biconditional).**  The chaining gate evaluates to zero
    across adjacent rows iff `icur(i) = ipre(i+1)` — the cross-row accumulator hand-off. -/
theorem reified_icur_chain_sound
    (minp : MemoryTable.Inputs K) (mop0 mop1 : MState → K)
    (mrow0 mrow1 : MemoryTable.Pub K) (mg0 mg1 : K) :
    icurChainExpr.eval (twoRow (Reified.memoryEnvFull minp mop0 mrow0 mg0)
                               (Reified.memoryEnvFull minp mop1 mrow1 mg1)) = 0
      ↔ mrow0.icur = mrow1.ipre := by
  show mrow0.icur - mrow1.ipre = 0 ↔ mrow0.icur = mrow1.ipre
  exact sub_eq_zero

/-- **Initial LogUp endpoint soundness (tight).**  The boundary gate evaluates to zero exactly when
    the first row's `ipre` accumulator is zero. -/
theorem memIpreInit_sound
    (minp : MemoryTable.Inputs K) (mop : MState → K)
    (mrow : MemoryTable.Pub K) (mg : K) :
    memIpreInitExpr.eval (Reified.memoryEnvFull minp mop mrow mg) = 0
      ↔ mrow.ipre = 0 := Iff.rfl

/-- **Terminal LogUp endpoint soundness (tight).**  The terminal gate evaluates to zero exactly
    when the last row's `icur` accumulator is zero. -/
theorem memIcurTerm_sound
    (minp : MemoryTable.Inputs K) (mop : MState → K)
    (mrow : MemoryTable.Pub K) (mg : K) :
    memIcurTermExpr.eval (Reified.memoryEnvFull minp mop mrow mg) = 0
      ↔ mrow.icur = 0 := Iff.rfl

/-- The two endpoint evaluations are jointly tight, for arbitrary concrete first and last rows. -/
theorem memEndpointGates_sound
    (minp : MemoryTable.Inputs K) (mopFirst mopLast : MState → K)
    (first last : MemoryTable.Pub K) (mgFirst mgLast : K) :
    (memIpreInitExpr.eval (Reified.memoryEnvFull minp mopFirst first mgFirst) = 0
      ∧ memIcurTermExpr.eval (Reified.memoryEnvFull minp mopLast last mgLast) = 0)
      ↔ (first.ipre = 0 ∧ last.icur = 0) :=
  and_congr (memIpreInit_sound minp mopFirst first mgFirst)
    (memIcurTerm_sound minp mopLast last mgLast)

end MemChain

/-! ### Compute line-nonce chaining `ln(i) = ln_prev(i+1)` (deliverable #4 — cols 66→65)

  The compute table's per-row log-nonce `ln` (column 66) is handed to the next row's `ln_prev`
  (column 65): the value committed as `ln` of row `i` must equal `ln_prev` of row `i+1`.  This is
  the compute-table analogue of `icurChainExpr`, structurally identical, and it is what forces the
  line-nonce column to chain across the whole compute table (the aggregate α-telescoping itself
  lives in the walk chip; this gate is the per-row hand-off substrate). -/

section CompChain
open ComputeTable Reified

/-- **Compute line-nonce chaining gate** `ln(i) − ln_prev(i+1)` (transition; degree 1). -/
def lnChainExpr : Expr := .Sub (Reified.tc 66) (tn 65)

/-- **`reified_ln_chain_sound` (tight biconditional).**  The line-nonce chaining gate evaluates to
    zero across adjacent rows iff `ln(i) = ln_prev(i+1)` — the cross-row line-nonce hand-off
    (analogue of `reified_icur_chain_sound`).  Independent of the challenge inputs / selector /
    decode / extra columns (the gate reads only cols 66/65). -/
theorem reified_ln_chain_sound
    (inp0 inp1 : ComputeTable.Inputs K) (op0 op1 : State → K)
    (pub0 pub1 : ComputeTable.Pub K) (dec0 dec1 : ComputeTable.Dec K)
    (ex0 ex1 : ComputeTable.Extra K) :
    lnChainExpr.eval (twoRow (Reified.computeEnvFull inp0 op0 pub0 dec0 ex0)
                             (Reified.computeEnvFull inp1 op1 pub1 dec1 ex1)) = 0
      ↔ pub0.ln = pub1.ln_prev := by
  show pub0.ln - pub1.ln_prev = 0 ↔ pub0.ln = pub1.ln_prev
  exact sub_eq_zero

end CompChain

/-! ### Walk α-telescoping transitions (reifying `Walk.WalkSat`)

  The walk columns (a family `ℕ → K`, row-indexed): `ln`, `count`, `acc`, the RLC-reduced current
  node `cur`, plus two committed helper columns — the per-row child RLC-sum
  `cc(i) = Σ_{l} α^l·chld'(i,l)` (`walkCC`) and the per-row count multiplier
  `cm(i) = α^{fanout(i)}` (`walkCM`).

  Walk column layout: 0=ln, 1=count, 2=acc, 3=cur, 4=cc, 5=cm; challenge 0 = α; public 0 =
  initial_count, public 1 = seed. -/

section Walk

variable {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
variable {ln cnt acc : ℕ → K} {α seed ic : K} {h : ℕ}

/-- Committed per-row child RLC-sum `cc(i) = Σ_{l=1}^{fanout(i)} α^l · chld'(i,l)`. -/
def walkCC (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (α : K) (i : ℕ) : K :=
  ∑ l ∈ Finset.Icc 1 (fo i), α ^ l * chld' i l
/-- Committed per-row count multiplier `cm(i) = α^{fanout(i)}`. -/
def walkCM (fo : ℕ → ℕ) (α : K) (i : ℕ) : K := α ^ (fo i)

theorem c_mul_walkCC (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (α : K) (c : K) (j : ℕ) :
    c * walkCC chld' fo α j = ∑ l ∈ Finset.Icc 1 (fo j), α ^ l * c * chld' j l := by
  rw [walkCC, Finset.mul_sum]; exact Finset.sum_congr rfl (fun l _ => by ring)

/-- A walk row environment at row `i`. -/
def walkRowEnv (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (ln cnt acc : ℕ → K) (α seed ic : K) (i : ℕ) : Env K where
  trace := fun j => match j with
    | 0 => ln i | 1 => cnt i | 2 => acc i | 3 => cur i
    | 4 => walkCC chld' fo α i | 5 => walkCM fo α i | _ => 0
  traceNext := fun _ => 0
  chal := fun j => match j with | 0 => α | _ => 0
  pub := fun j => match j with | 0 => ic | 1 => seed | _ => 0

/-- Shorthand for the two-row walk env at step `i`. -/
def walkStep (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (ln cnt acc : ℕ → K) (α seed ic : K) (i : ℕ) : Env K :=
  twoRow (walkRowEnv cur chld' fo ln cnt acc α seed ic i)
         (walkRowEnv cur chld' fo ln cnt acc α seed ic (i + 1))

/-- Line increment (transition): `ln(i+1) − α·ln(i)`. -/
def walkLnStep : Expr := .Sub (tn 0) (.Mul (Reified.chl 0) (Reified.tc 0))
/-- Count increment (transition): `count(i+1) − count(i)·cm(i+1)`. -/
def walkCountStep : Expr := .Sub (tn 1) (.Mul (Reified.tc 1) (tn 5))
/-- Accumulation step (transition): `ln(i+1)·cur(i+1) + acc(i+1) − acc(i) − count(i)·cc(i+1)`. -/
def walkAccStep : Expr :=
  .Sub (.Sub (.Add (.Mul (tn 0) (tn 3)) (tn 2)) (Reified.tc 2)) (.Mul (Reified.tc 1) (tn 4))
/-- Initial line (boundary): `ln(1) − α`. -/
def walkLn1 : Expr := .Sub (Reified.tc 0) (Reified.chl 0)
/-- Initial count (boundary): `count(1) − initial_count·cm(1)`. -/
def walkCount1 : Expr := .Sub (Reified.tc 1) (.Mul (pubv 0) (Reified.tc 5))
/-- Initial accumulator (boundary): `ln(1)·cur(1) + acc(1) − (initial_count·cc(1) + seed)`. -/
def walkAccInit : Expr :=
  .Sub (.Add (.Mul (Reified.tc 0) (Reified.tc 3)) (Reified.tc 2))
       (.Add (.Mul (pubv 0) (Reified.tc 4)) (pubv 1))
/-- Terminal `out_walk = acc(h)` (terminal). -/
def walkOut : Expr := Reified.tc 2

/-- Local walk env with per-row root mask at index `6`.  The seed public is
    retained in the env (unused by the masked exprs) so the hosted subst
    continues to type; the deployed chip drops the seed read. -/
def walkRowEnvMasked (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (ln cnt acc : ℕ → K) (α seed ic : K) (rm : ℕ → K) (i : ℕ) : Env K where
  trace := fun j => match j with
    | 0 => ln i | 1 => cnt i | 2 => acc i | 3 => cur i
    | 4 => walkCC chld' fo α i | 5 => walkCM fo α i | 6 => rm i | _ => 0
  traceNext := fun _ => 0
  chal := fun j => match j with | 0 => α | _ => 0
  pub := fun j => match j with | 0 => ic | 1 => seed | _ => 0

/-- Two-row masked walk env at step `i`. -/
def walkStepMasked (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (ln cnt acc : ℕ → K) (α seed ic : K) (rm : ℕ → K) (i : ℕ) : Env K :=
  twoRow (walkRowEnvMasked cur chld' fo ln cnt acc α seed ic rm i)
         (walkRowEnvMasked cur chld' fo ln cnt acc α seed ic rm (i + 1))

/-- **Masked** initial accumulator: first row is a root
    whenever `kMem ≥ 1`, so `acc(1) − initial_count·cc(1)` with no product. -/
def walkAccInitMasked : Expr :=
  .Sub (Reified.tc 2) (.Mul (pubv 0) (Reified.tc 4))

/-- **Masked** accumulation step: `(1−rm(i+1))·ln(i+1)·cur(i+1) + acc(i+1) − acc(i)
    − count(i)·cc(i+1)`. -/
def walkAccStepMasked : Expr :=
  .Sub (.Sub (.Add (.Mul (.Mul (.Sub (.Const 1) (tn 6)) (tn 0)) (tn 3)) (tn 2))
            (Reified.tc 2))
       (.Mul (Reified.tc 1) (tn 4))

theorem reified_walk_ln_step_sound (i : ℕ) :
    walkLnStep.eval (walkStep cur chld' fo ln cnt acc α seed ic i) = 0 ↔ ln (i + 1) = α * ln i := by
  show ln (i + 1) - α * ln i = 0 ↔ ln (i + 1) = α * ln i
  exact sub_eq_zero

theorem reified_walk_count_step_sound (i : ℕ) :
    walkCountStep.eval (walkStep cur chld' fo ln cnt acc α seed ic i) = 0
      ↔ cnt (i + 1) = cnt i * α ^ (fo (i + 1)) := by
  show cnt (i + 1) - cnt i * α ^ (fo (i + 1)) = 0 ↔ cnt (i + 1) = cnt i * α ^ (fo (i + 1))
  exact sub_eq_zero

theorem reified_walk_acc_step_sound (i : ℕ) :
    walkAccStep.eval (walkStep cur chld' fo ln cnt acc α seed ic i) = 0
      ↔ ln (i + 1) * cur (i + 1) + acc (i + 1) - acc i
          = ∑ l ∈ Finset.Icc 1 (fo (i + 1)), α ^ l * cnt i * chld' (i + 1) l := by
  show ln (i + 1) * cur (i + 1) + acc (i + 1) - acc i - cnt i * walkCC chld' fo α (i + 1) = 0
      ↔ ln (i + 1) * cur (i + 1) + acc (i + 1) - acc i
          = ∑ l ∈ Finset.Icc 1 (fo (i + 1)), α ^ l * cnt i * chld' (i + 1) l
  rw [c_mul_walkCC]; exact sub_eq_zero

theorem reified_walk_ln1_sound :
    walkLn1.eval (walkRowEnv cur chld' fo ln cnt acc α seed ic 1) = 0 ↔ ln 1 = α := by
  show ln 1 - α = 0 ↔ ln 1 = α
  exact sub_eq_zero

theorem reified_walk_count1_sound :
    walkCount1.eval (walkRowEnv cur chld' fo ln cnt acc α seed ic 1) = 0
      ↔ cnt 1 = ic * α ^ (fo 1) := by
  show cnt 1 - ic * α ^ (fo 1) = 0 ↔ cnt 1 = ic * α ^ (fo 1)
  exact sub_eq_zero

theorem reified_walk_accInit_sound :
    walkAccInit.eval (walkRowEnv cur chld' fo ln cnt acc α seed ic 1) = 0
      ↔ ln 1 * cur 1 + acc 1
          = (∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * ic * chld' 1 l) + seed := by
  show ln 1 * cur 1 + acc 1 - (ic * walkCC chld' fo α 1 + seed) = 0
      ↔ ln 1 * cur 1 + acc 1 = (∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * ic * chld' 1 l) + seed
  rw [c_mul_walkCC]; exact sub_eq_zero

theorem reified_walk_out_sound :
    walkOut.eval (walkRowEnv cur chld' fo ln cnt acc α seed ic h) = 0 ↔ acc h = 0 := Iff.rfl

theorem reified_walk_accInitMasked_sound (rm : ℕ → K) :
    walkAccInitMasked.eval (walkRowEnvMasked cur chld' fo ln cnt acc α seed ic rm 1) = 0
      ↔ acc 1 = ∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * ic * chld' 1 l := by
  simp [walkAccInitMasked, walkRowEnvMasked, Expr.eval, Reified.tc, pubv]
  rw [c_mul_walkCC]
  exact sub_eq_zero

theorem reified_walk_acc_stepMasked_sound (rm : ℕ → K) (i : ℕ) :
    walkAccStepMasked.eval (walkStepMasked cur chld' fo ln cnt acc α seed ic rm i) = 0
      ↔ (1 - rm (i + 1)) * ln (i + 1) * cur (i + 1) + acc (i + 1) - acc i
          = ∑ l ∈ Finset.Icc 1 (fo (i + 1)), α ^ l * cnt i * chld' (i + 1) l := by
  simp [walkAccStepMasked, walkStepMasked, twoRow, walkRowEnvMasked, Expr.eval,
    Reified.tc, tn, pubv]
  rw [c_mul_walkCC]
  exact sub_eq_zero

theorem walkLn1_eval_masked (rm : ℕ → K) :
    walkLn1.eval (walkRowEnvMasked cur chld' fo ln cnt acc α seed ic rm 1)
      = walkLn1.eval (walkRowEnv cur chld' fo ln cnt acc α seed ic 1) := by
  simp [walkLn1, walkRowEnvMasked, walkRowEnv, Expr.eval, Reified.tc, Reified.chl]

theorem walkCount1_eval_masked (rm : ℕ → K) :
    walkCount1.eval (walkRowEnvMasked cur chld' fo ln cnt acc α seed ic rm 1)
      = walkCount1.eval (walkRowEnv cur chld' fo ln cnt acc α seed ic 1) := by
  simp [walkCount1, walkRowEnvMasked, walkRowEnv, Expr.eval, Reified.tc, pubv]

theorem walkLnStep_eval_masked (rm : ℕ → K) (i : ℕ) :
    walkLnStep.eval (walkStepMasked cur chld' fo ln cnt acc α seed ic rm i)
      = walkLnStep.eval (walkStep cur chld' fo ln cnt acc α seed ic i) := by
  simp [walkLnStep, walkStepMasked, walkStep, twoRow, walkRowEnvMasked, walkRowEnv,
    Expr.eval, Reified.tc, tn, Reified.chl]

theorem walkCountStep_eval_masked (rm : ℕ → K) (i : ℕ) :
    walkCountStep.eval (walkStepMasked cur chld' fo ln cnt acc α seed ic rm i)
      = walkCountStep.eval (walkStep cur chld' fo ln cnt acc α seed ic i) := by
  simp [walkCountStep, walkStepMasked, walkStep, twoRow, walkRowEnvMasked, walkRowEnv,
    Expr.eval, Reified.tc, tn]

/-- **`reified_walk_sound` (tight biconditional).**  `Walk.WalkSat` (the entire arithmetized walk:
    init + line/count/accumulation recurrences) holds **iff** all the reified walk gates
    (`.boundary` at row 1, `.transition` over rows `1..h−1`) evaluate to zero — a faithful,
    genuinely cross-row reflection: the transition gates really read `traceNext`. -/
theorem reified_walk_sound :
    Walk.WalkSat cur chld' fo ln cnt acc α seed ic h
      ↔ (1 ≤ h
          ∧ walkLn1.eval (walkRowEnv cur chld' fo ln cnt acc α seed ic 1) = 0
          ∧ walkCount1.eval (walkRowEnv cur chld' fo ln cnt acc α seed ic 1) = 0
          ∧ walkAccInit.eval (walkRowEnv cur chld' fo ln cnt acc α seed ic 1) = 0
          ∧ (∀ i, 1 ≤ i → i < h →
                walkLnStep.eval (walkStep cur chld' fo ln cnt acc α seed ic i) = 0
              ∧ walkCountStep.eval (walkStep cur chld' fo ln cnt acc α seed ic i) = 0
              ∧ walkAccStep.eval (walkStep cur chld' fo ln cnt acc α seed ic i) = 0)) := by
  constructor
  · intro hw
    refine ⟨hw.hpos,
      reified_walk_ln1_sound.mpr hw.ln1,
      reified_walk_count1_sound.mpr hw.count1,
      reified_walk_accInit_sound.mpr hw.accInit,
      fun i h1 h2 => ⟨(reified_walk_ln_step_sound i).mpr (hw.lnInc i h1 h2),
                      (reified_walk_count_step_sound i).mpr (hw.countInc i h1 h2),
                      (reified_walk_acc_step_sound i).mpr (hw.accStep i h1 h2)⟩⟩
  · rintro ⟨hpos, hln1, hc1, hai, hstep⟩
    exact
      { hpos := hpos
        ln1 := reified_walk_ln1_sound.mp hln1
        count1 := reified_walk_count1_sound.mp hc1
        accInit := reified_walk_accInit_sound.mp hai
        lnInc := fun i h1 h2 => (reified_walk_ln_step_sound i).mp (hstep i h1 h2).1
        countInc := fun i h1 h2 => (reified_walk_count_step_sound i).mp (hstep i h1 h2).2.1
        accStep := fun i h1 h2 => (reified_walk_acc_step_sound i).mp (hstep i h1 h2).2.2 }

end Walk

/-! ### IO accumulator transitions (reifying `IO.ProgIOSat` / `IO.MemIOSat`)

  The IO log-derivative accumulators live over `K = RatFunc L` (`L = 𝔽(Y)`).  Since `Expr` has no
  division, the per-row `frac c = 1/(X+c)` contribution appears in trace column 1.  In the current
  raw verifier this column is not prover-committed independently: the row environments and
  verifier trace construction supply the honest value `SetEq.frac c`.  There is no inverse gate in
  this symbolic `RatFunc` AIR.  A finite-`K`, prover-committed replacement would need such an
  inverse gate.  Prog columns: 0=acc, 1=frac(a i); public 0 = requests.  Mem columns: 0=acc, 1=frac(b i),
  2=`algebraMap 𝔽(Y)[X] 𝔽(X,Y) (C μ(i))` (the cast multiplicity, so `μ • frac = col2·col1` by
  `SetEq.smul_frac`); public 0 = responses, 1 = out_mem. -/

section IOTrans

variable {L : Type*} [Field L]
variable {a b μ : ℕ → L} {accP accM : ℕ → RatFunc L} {requests responses out_mem : RatFunc L}

/-- Prog-IO accumulator row environment. -/
noncomputable def ioProgRowEnv (a : ℕ → L) (acc : ℕ → RatFunc L) (requests : RatFunc L)
    (i : ℕ) : Env (RatFunc L) where
  trace := fun j => match j with | 0 => acc i | 1 => SetEq.frac (a i) | _ => 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun j => match j with | 0 => requests | _ => 0

/-- Mem-IO accumulator row environment. -/
noncomputable def ioMemRowEnv (b μ : ℕ → L) (acc : ℕ → RatFunc L)
    (responses out_mem : RatFunc L) (i : ℕ) : Env (RatFunc L) where
  trace := fun j => match j with
    | 0 => acc i | 1 => SetEq.frac (b i)
    | 2 => algebraMap (Polynomial L) (RatFunc L) (Polynomial.C (μ i)) | _ => 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun j => match j with | 0 => responses | 1 => out_mem | _ => 0

/-- Prog accumulation step (transition): `acc(i+1) − acc(i) − frac(a i)`. -/
def ioProgStep : Expr := .Sub (.Sub (tn 0) (Reified.tc 0)) (Reified.tc 1)
/-- Prog init (boundary): `acc(0)`. -/
def ioProgInit : Expr := Reified.tc 0
/-- Prog terminal: `requests − acc(k₁)`. -/
def ioProgTerm : Expr := .Sub (pubv 0) (Reified.tc 0)
/-- Mem accumulation step (transition): `acc(i+1) − acc(i) + μ(i)·frac(b i)`. -/
def ioMemStep : Expr := .Add (.Sub (tn 0) (Reified.tc 0)) (.Mul (Reified.tc 2) (Reified.tc 1))
/-- Mem init (boundary): `acc(0) − responses`. -/
def ioMemInit : Expr := .Sub (Reified.tc 0) (pubv 0)
/-- Mem terminal: `out_mem − acc(k₂)`. -/
def ioMemTerm : Expr := .Sub (pubv 1) (Reified.tc 0)

theorem reified_io_prog_step_sound (i : ℕ) :
    ioProgStep.eval (twoRow (ioProgRowEnv a accP requests i) (ioProgRowEnv a accP requests (i+1))) = 0
      ↔ accP (i + 1) = accP i + SetEq.frac (a i) := by
  show accP (i + 1) - accP i - SetEq.frac (a i) = 0 ↔ accP (i + 1) = accP i + SetEq.frac (a i)
  rw [sub_sub, sub_eq_zero]

theorem reified_io_prog_init_sound :
    ioProgInit.eval (ioProgRowEnv a accP requests 0) = 0 ↔ accP 0 = 0 := Iff.rfl

theorem reified_io_prog_term_sound (k₁ : ℕ) :
    ioProgTerm.eval (ioProgRowEnv a accP requests k₁) = 0 ↔ requests = accP k₁ := by
  show requests - accP k₁ = 0 ↔ requests = accP k₁
  exact sub_eq_zero

/-- **`reified_io_prog_sound` (tight biconditional).**  `IO.ProgIOSat` holds iff the reified
    prog-IO gates (boundary init, transition steps, terminal) all evaluate to zero. -/
theorem reified_io_prog_sound (k₁ : ℕ) :
    IO.ProgIOSat a accP requests k₁
      ↔ (ioProgInit.eval (ioProgRowEnv a accP requests 0) = 0
          ∧ (∀ i, i < k₁ →
                ioProgStep.eval (twoRow (ioProgRowEnv a accP requests i)
                                        (ioProgRowEnv a accP requests (i+1))) = 0)
          ∧ ioProgTerm.eval (ioProgRowEnv a accP requests k₁) = 0) := by
  constructor
  · intro hP
    exact ⟨reified_io_prog_init_sound.mpr hP.init,
           fun i hi => (reified_io_prog_step_sound i).mpr (hP.step i hi),
           (reified_io_prog_term_sound k₁).mpr hP.term⟩
  · rintro ⟨hi, hs, ht⟩
    exact { init := reified_io_prog_init_sound.mp hi
            step := fun i hi' => (reified_io_prog_step_sound i).mp (hs i hi')
            term := (reified_io_prog_term_sound k₁).mp ht }

theorem reified_io_mem_step_sound (i : ℕ) :
    ioMemStep.eval (twoRow (ioMemRowEnv b μ accM responses out_mem i)
                           (ioMemRowEnv b μ accM responses out_mem (i+1))) = 0
      ↔ accM (i + 1) = accM i - μ i • SetEq.frac (b i) := by
  show accM (i + 1) - accM i
        + algebraMap (Polynomial L) (RatFunc L) (Polynomial.C (μ i)) * SetEq.frac (b i) = 0
      ↔ accM (i + 1) = accM i - μ i • SetEq.frac (b i)
  rw [← SetEq.smul_frac]
  constructor
  · intro hh; linear_combination hh
  · intro hh; linear_combination hh

theorem reified_io_mem_init_sound :
    ioMemInit.eval (ioMemRowEnv b μ accM responses out_mem 0) = 0 ↔ accM 0 = responses := by
  show accM 0 - responses = 0 ↔ accM 0 = responses
  exact sub_eq_zero

theorem reified_io_mem_term_sound (k₂ : ℕ) :
    ioMemTerm.eval (ioMemRowEnv b μ accM responses out_mem k₂) = 0 ↔ out_mem = accM k₂ := by
  show out_mem - accM k₂ = 0 ↔ out_mem = accM k₂
  exact sub_eq_zero

/-- **`reified_io_mem_sound` (tight biconditional).**  `IO.MemIOSat` holds iff the reified
    mem-IO gates (boundary init, transition steps, terminal) all evaluate to zero. -/
theorem reified_io_mem_sound (k₂ : ℕ) :
    IO.MemIOSat b μ accM responses out_mem k₂
      ↔ (ioMemInit.eval (ioMemRowEnv b μ accM responses out_mem 0) = 0
          ∧ (∀ i, i < k₂ →
                ioMemStep.eval (twoRow (ioMemRowEnv b μ accM responses out_mem i)
                                       (ioMemRowEnv b μ accM responses out_mem (i+1))) = 0)
          ∧ ioMemTerm.eval (ioMemRowEnv b μ accM responses out_mem k₂) = 0) := by
  constructor
  · intro hM
    exact ⟨reified_io_mem_init_sound.mpr hM.init,
           fun i hi => (reified_io_mem_step_sound i).mpr (hM.step i hi),
           (reified_io_mem_term_sound k₂).mpr hM.term⟩
  · rintro ⟨hi, hs, ht⟩
    exact { init := reified_io_mem_init_sound.mp hi
            step := fun i hi' => (reified_io_mem_step_sound i).mp (hs i hi')
            term := (reified_io_mem_term_sound k₂).mp ht }

/-! ### Deliverable #2 — the reified IO gates SUPPLY the `ProgIOSat`/`MemIOSat` witnesses

  `V_NockVMROM_forest` conjunct (3) is a biconditional whose LHS existentially quantifies over
  `ProgIOSat`/`MemIOSat` accumulators.  These two lemmas make the exported IO gates the genuine
  SOURCE of those witnesses: from satisfaction of the reified `ioProgAIR`/`ioMemAIR` gates, we
  PRODUCE the proven accumulator predicates (via `reified_io_prog_sound`/`reified_io_mem_sound`).
  The upgraded bridge uses them to populate the existential — so deleting `reified_io_*_sound`
  breaks the bridge (the witnesses can no longer be built from the gates). -/

section IOSupply
variable {L : Type*} [Field L]

/-- **Exported prog-IO gates ⟹ `ProgIOSat`.**  Satisfaction of the `ioProgAIR` gates (boundary
    init at row 0, transition steps over rows `< k₁`, terminal at `k₁`) supplies the proven
    accumulator predicate `IO.ProgIOSat`.  Directly `reified_io_prog_sound.mpr`. -/
theorem exported_ioProg_gives_ProgIOSat (a : ℕ → L) (accP : ℕ → RatFunc L)
    (requests : RatFunc L) (k₁ : ℕ)
    (hinit : ioProgInit.eval (ioProgRowEnv a accP requests 0) = 0)
    (hstep : ∀ i, i < k₁ →
        ioProgStep.eval (twoRow (ioProgRowEnv a accP requests i)
                                (ioProgRowEnv a accP requests (i + 1))) = 0)
    (hterm : ioProgTerm.eval (ioProgRowEnv a accP requests k₁) = 0) :
    IO.ProgIOSat a accP requests k₁ :=
  (reified_io_prog_sound k₁).mpr ⟨hinit, hstep, hterm⟩

/-- **Exported mem-IO gates ⟹ `MemIOSat`.**  Satisfaction of the `ioMemAIR` gates supplies the
    proven accumulator predicate `IO.MemIOSat`.  Directly `reified_io_mem_sound.mpr`. -/
theorem exported_ioMem_gives_MemIOSat (b μ : ℕ → L) (accM : ℕ → RatFunc L)
    (responses out_mem : RatFunc L) (k₂ : ℕ)
    (hinit : ioMemInit.eval (ioMemRowEnv b μ accM responses out_mem 0) = 0)
    (hstep : ∀ i, i < k₂ →
        ioMemStep.eval (twoRow (ioMemRowEnv b μ accM responses out_mem i)
                               (ioMemRowEnv b μ accM responses out_mem (i + 1))) = 0)
    (hterm : ioMemTerm.eval (ioMemRowEnv b μ accM responses out_mem k₂) = 0) :
    IO.MemIOSat b μ accM responses out_mem k₂ :=
  (reified_io_mem_sound k₂).mpr ⟨hinit, hstep, hterm⟩

end IOSupply

end IOTrans

/-! ### The exported transition AIRs (deliverable #5: JSON incl. `.transition`/`.boundary`/`.terminal`)

  Each recurrence becomes a small backend-neutral `AIR` value, tagged with the Plonky3 gating
  (`.boundary → when_first_row`, `.transition → when_transition`, `.terminal → when_last_row`).
  The memory transition and zero endpoints are folded onto the existing row-local `(memoryAIR (K := K))` as
  `memoryAIRchained`, turning the memory table into a genuinely end-to-end machine (closed chained
  accumulator). -/

/-- Walk AIR: 3 `.boundary` + 3 `.transition` + 1 `.terminal`. -/
def walkAIR : AIR where
  numTraceCols  := 6
  numChallenges := 1
  numPublic     := 2
  constraints :=
    [ ⟨.boundary, walkLn1⟩, ⟨.boundary, walkCount1⟩, ⟨.boundary, walkAccInit⟩,
      ⟨.transition, walkLnStep⟩, ⟨.transition, walkCountStep⟩, ⟨.transition, walkAccStep⟩,
      ⟨.terminal, walkOut⟩ ]

/-- Prog-IO accumulator AIR. -/
def ioProgAIR : AIR where
  numTraceCols  := 2
  numChallenges := 0
  numPublic     := 1
  constraints := [⟨.boundary, ioProgInit⟩, ⟨.transition, ioProgStep⟩, ⟨.terminal, ioProgTerm⟩]

/-- Mem-IO accumulator AIR. -/
def ioMemAIR : AIR where
  numTraceCols  := 3
  numChallenges := 0
  numPublic     := 2
  constraints := [⟨.boundary, ioMemInit⟩, ⟨.transition, ioMemStep⟩, ⟨.terminal, ioMemTerm⟩]

/-- **Memory axis-accumulator SEED boundary** (`.boundary` = `when_first_row`, i.e. the walk root).
    At the seed row the axis accumulators start empty: `axis_counts = axis_indicator = 0`
    (cols 8, 7).  The memory table is a `RAP_walk` instance whose root label is the PUBLIC seed:
    `RAP_walk`'s initial-input constraints pin the seed's label (the paper`ln(1) = α`
    at `:814`), `𝓛𝒯_mem`'s node label includes `axis_indicator`/`axis_counts` (`:1408`), and
    `Corr:forest` (`:1004`) fixes the seed over the labelled roots — so the root value of the two
    accumulators is the seed input, not a free `V_mem` column.  This is the INITIAL-value analogue
    of the halt-leaf `axis_counts = axis_indicator = 0` idiom;
    the `intermediate` accumulator's initial-zero of `:1431` is a different gate
    (`memIpreInitExpr`).  It is SOUNDNESS-CRITICAL for the axis columns specifically: a wrong
    committed `mem.axis` leaves a nonzero residual at the WALK ROOT, not at the halt leaves
    (which stay structurally `0`), so it is THIS seed gate — not the halt gate — that rejects
    it (`StrengtheningScope.wrong_axis_satisfies_every_rowlocal_constraint`).  Discharges the
    `rootPt.counts = 0` obligation carried by `AxisBridge.axis_lookups_valid_endToEnd`
    (`Reified.Trans.memSeedBoundary_sound` + `AxisBridge.seedGate_gives_rootPt_zero` +
    `AxisBridge.axis_lookups_valid_endToEnd_of_seedGate`, and the `RootAxisBoundaryAt` chain of
    `ProductionP8Containment.lean`). -/
def memSeedCountsExpr : Expr := Reified.tc 8

def memSeedIndicatorExpr : Expr := Reified.tc 7

/-- The two seed-boundary expressions, gated `.boundary` (first row = walk root). -/
def memSeedBoundaryExprs : List Expr := [memSeedCountsExpr, memSeedIndicatorExpr]

/-- **Seed-boundary soundness (tight).**  The gate list evaluates to zero at a row iff that row's
    parent axis accumulators (`axis_counts`, `axis_indicator`) are both zero — the seed row is
    axis-empty.  Proven directly from the `rfl` column-read lemmas `eval_mPtCnt`/`eval_mPtInd`. -/
theorem memSeedBoundary_sound
    (minp : MemoryTable.Inputs K) (mop : MemoryTable.MState → K) (mrow : MemoryTable.Pub K)
    (mg : K) :
    (∀ e ∈ memSeedBoundaryExprs, e.eval (Reified.memoryEnvFull minp mop mrow mg) = 0)
      ↔ (mrow.pt.counts = 0 ∧ mrow.pt.indicator = 0) := by
  simp only [memSeedBoundaryExprs, memSeedCountsExpr, memSeedIndicatorExpr,
    List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
    Reified.eval_mPtCnt, Reified.eval_mPtInd]

/-- **`memoryAIRchained`** — the row-local `(memoryAIR (K := K))`; the cross-row LogUp chaining `.transition`
    gate `icur(i) = ipre(i+1)`; the two axis-accumulator seed `.boundary` gates
    `axis_counts = axis_indicator = 0` at the walk root;
    and the LogUp endpoint gates `ipre(first) = 0` (`.boundary`) and `icur(last) = 0` (`.terminal`).
    The axis seed and LogUp seed are distinct constraints over columns 8/7 and 31 respectively.
    ⚠️ NOTE: the transition/endpoint layer is not yet consumed by `fullAIR_entails_forest` (which
    still uses plain `(memoryAIR (K := K))`); folding it in is Tier A.2 (see the `Trans` section docstring). -/
noncomputable def memoryAIRchained : AIR :=
  { (Reified.memoryAIR (K := K)) with
    constraints := (Reified.memoryAIR (K := K)).constraints ++ [⟨.transition, icurChainExpr⟩]
      ++ memSeedBoundaryExprs.map (fun e => (⟨.boundary, e⟩ : Constraint))
      ++ [⟨.boundary, memIpreInitExpr⟩, ⟨.terminal, memIcurTermExpr⟩] }

/-- **`computeAIRchained`** — the row-local `computeAIR` plus the cross-row line-nonce hand-off
    `.transition` gate `ln(i) = ln_prev(i+1)` (cols 66→65), the compute-table analogue of
    `memoryAIRchained` (deliverable #4).  Consumed by `fullAIR_entails_forest'` (the ln hand-off
    is derived FROM this gate via `reified_ln_chain_sound`). -/
def computeAIRchained : AIR :=
  { Reified.computeAIR with
    constraints := Reified.computeAIR.constraints ++ [⟨.transition, lnChainExpr⟩] }

/-- The line-nonce hand-off gate is genuinely one of `computeAIRchained`'s constraints. -/
theorem lnChain_mem_computeAIRchained :
    (⟨.transition, lnChainExpr⟩ : Constraint) ∈ computeAIRchained.constraints := by
  simp [computeAIRchained]

/-- The icur hand-off gate is genuinely one of `memoryAIRchained`'s constraints. -/
theorem icurChain_mem_memoryAIRchained :
    (⟨.transition, icurChainExpr⟩ : Constraint) ∈ (memoryAIRchained (K := K)).constraints := by
  simp [memoryAIRchained]

/-- The axis-`counts` seed boundary gate is genuinely one of `memoryAIRchained`'s constraints. -/
theorem memSeedCounts_mem_memoryAIRchained :
    (⟨.boundary, memSeedCountsExpr⟩ : Constraint) ∈ (memoryAIRchained (K := K)).constraints := by
  simp [memoryAIRchained, memSeedBoundaryExprs]

/-- The axis-`indicator` seed boundary gate is genuinely one of `memoryAIRchained`'s constraints. -/
theorem memSeedIndicator_mem_memoryAIRchained :
    (⟨.boundary, memSeedIndicatorExpr⟩ : Constraint) ∈ (memoryAIRchained (K := K)).constraints := by
  simp [memoryAIRchained, memSeedBoundaryExprs]

/-- The LogUp `ipre = 0` initial gate is genuinely one of `memoryAIRchained`'s constraints. -/
theorem memIpreInit_mem_memoryAIRchained :
    (⟨.boundary, memIpreInitExpr⟩ : Constraint) ∈ (memoryAIRchained (K := K)).constraints := by
  simp [memoryAIRchained]

/-- The LogUp `icur = 0` terminal gate is genuinely one of `memoryAIRchained`'s constraints. -/
theorem memIcurTerm_mem_memoryAIRchained :
    (⟨.terminal, memIcurTermExpr⟩ : Constraint) ∈ (memoryAIRchained (K := K)).constraints := by
  simp [memoryAIRchained]

def exportWalkAIR : IO Unit := IO.println (AIR.toJson walkAIR)
def exportIOProgAIR : IO Unit := IO.println (AIR.toJson ioProgAIR)
def exportIOMemAIR : IO Unit := IO.println (AIR.toJson ioMemAIR)
noncomputable def exportMemoryAIRchained : IO Unit :=
  IO.println (AIR.toJson (memoryAIRchained (K := K)))
def exportComputeAIRchained : IO Unit := IO.println (AIR.toJson computeAIRchained)

#eval exportWalkAIR
#eval exportIOProgAIR
#eval exportIOMemAIR
#eval exportComputeAIRchained
#eval s!"walkAIR: maxDegree = {walkAIR.maxDegree}, #constraints = {walkAIR.constraints.length} (transition-active)"
#eval s!"ioProgAIR: maxDegree = {ioProgAIR.maxDegree}, #constraints = {ioProgAIR.constraints.length}"
#eval s!"ioMemAIR: maxDegree = {ioMemAIR.maxDegree}, #constraints = {ioMemAIR.constraints.length}"

/-! ### The payoff bridge — exported AIR entails the Sprint-14 composed capstone (deliverable #3)

  The forward (soundness) direction: satisfaction of the exported AIR ENTAILS the hypotheses that
  the composed capstone `NockVM.V_NockVMROM_forest` consumes.

  What the bridge `fullAIR_entails_forest` ACTUALLY discharges (honest scope — spec-redteam):
    * ONLY the per-row `∃ ex, RAPcomp` / `∃ g, RAPmem` hypotheses (`hRc`/`hRm`'s first conjunct),
      DERIVED from the row-local `computeAIR`/`(memoryAIR (K := K))` soundness (`computeAIR_toRAP`,
      `memoryAIR_toRAP`) — see `exported_compute_rows_give_hRc` / `exported_memory_rows_give_hRm`.
      This is what a row-local-only bridge already gives; the bridge uses plain `computeAIR`/
      `(memoryAIR (K := K))`.

  ⚠️ SCOPE — the transition layer is FAITHFUL BUT NOT YET LOAD-BEARING (spec-redteam, Tier A).
  The reified transition AIRs (`walkAIR`/`ioProgAIR`/`ioMemAIR`/`memoryAIRchained`) and their
  soundness lemmas (`reified_walk_sound`/`reified_io_prog_sound`/`reified_io_mem_sound`/
  `reified_icur_chain_sound`/`memEndpointGates_sound`) are proven by TIGHT BICONDITIONALS to the
  corresponding cross-row recurrences and endpoint values — but they are proven IN ISOLATION and appear
  NOWHERE in `fullAIR_entails_forest` (not in its hypotheses, proof term, or conclusion).  The
  reason: `V_NockVMROM_forest` bakes `WalkSat` *inside* `walkBad`'s acceptance predicate and
  `walkBad_prob` never takes it as a hypothesis; conjunct (3) characterizes the `ProgIOSat`/
  `MemIOSat` existential via `io_result_LIO` with no hypothesis slot to plug a reified version in.
  So today the exported transition constraints sit ALONGSIDE the composed soundness, not inside it.
  Making them load-bearing — re-expressing `walkBad`/`walkBadForest` over the (challenge-
  instantiated) reified gates via `reified_walk_sound`, producing the IO witnesses from
  `ioProgAIR`/`ioMemAIR` satisfaction, and folding in `memoryAIRchained` — is **Tier A.2**.
  Not a soundness bug (nothing false; the transitions are faithful); a framing/plumbing gap.

  Also un-reified (follow-up, not flagged elsewhere): the compute table's cross-row line-nonce
  hand-off `ln_prev(i+1) = ln(i)` (cols 65/66) — structurally identical to `icurChainExpr`; not
  required by the bridge (aggregate telescoping lives in the walk chip), but noted for Tier A.2.

  What remains ASSUMED (exactly as `V_NockVMROM_forest` assumes it — NOT expressible as a local
  polynomial gate): the tree-STRUCTURAL side conditions — `Sf`-tiling (`hSfc`/`hSfm`), BFS-validity
  (`hvalidc`/`hvalidm`), arity bounds, the state/fanout matching (`hStatec`/`hFanc`, `hStatem`/
  `hFanm`), the **child-content link**, encoder injectivity, and
  the IO range/`Nodup` conditions.  These non-row-local structural antecedents are all discharged by
  the SAME future work: the position-free `α^i` BFT multiset in the walk chip forcing a committed
  child row's columns to equal the parent's declared child slot (NOT an adjacency `twoRow` gate —
  parent and child are non-adjacent BFS rows, which would need a §0-forbidden pointer).  The `z^i`
  axis-batching SOUNDNESS is the separate research item; we provide only the
  transition substrate it will run over. -/

section Bridge

variable {K : Type*} [Field K]

/-- Per-row: honest `computeAIR` satisfaction yields `∃ ex, RAPcomp` (drops the `z ≠ 0` bonus). -/
theorem row_computeAIR_gives_RAP
    (inp : ComputeTable.Inputs K) (pub : ComputeTable.Pub K) (dec : ComputeTable.Dec K)
    (ex : ComputeTable.Extra K)
    (hrow : ∀ c ∈ Reified.computeAIR.constraints,
        c.expr.eval (Reified.computeEnvFull inp (ComputeTable.opSel pub.state) pub dec ex) = 0) :
    ∃ ex', ComputeTable.RAPcomp inp pub dec ex' :=
  ⟨ex, Reified.computeAIR_toRAP inp pub dec ex hrow⟩

/-- Per-row: honest `(memoryAIR (K := K))` satisfaction yields `∃ g, RAPmem`. -/
theorem row_memoryAIR_gives_RAP
    (minp : MemoryTable.Inputs K) (mrow : MemoryTable.Pub K) (mg : K)
    (hrow : ∀ c ∈ (Reified.memoryAIR (K := K)).constraints,
        c.expr.eval (Reified.memoryEnvFull minp (MemoryTable.opSel mrow.st) mrow mg) = 0) :
    ∃ g, MemoryTable.RAPmem minp mrow g :=
  ⟨mg, Reified.memoryAIR_toRAP minp mrow mg hrow⟩

variable [Fintype K] [DecidableEq K]

/-- **`exported_compute_rows_give_hRc`.**  Per-row `computeAIR` satisfaction (honest selector) plus
    the structural state/fanout facts PRODUCE the exact per-row hypothesis `hRc` of
    `V_NockVMROM_forest` — i.e. the exported compute-chip AIR entails the capstone's compute-row
    hypothesis. -/
theorem exported_compute_rows_give_hRc
    (lblc : ℕ → State × ComputeTable.DTcomp K) (clabc : ℕ → ℕ → State × ComputeTable.DTcomp K)
    (foc : ℕ → ℕ) (hc : ℕ)
    (hAIRc : ∀ i, 1 ≤ i → i ≤ hc → ∃ ex : ComputeTable.Extra K,
        ∀ c ∈ Reified.computeAIR.constraints,
          c.expr.eval (Reified.computeEnvFull (lblc i).2.1
            (ComputeTable.opSel (lblc i).2.2.1.state) (lblc i).2.2.1 (lblc i).2.2.2 ex) = 0)
    (hStatec : ∀ i, 1 ≤ i → i ≤ hc → (lblc i).2.2.1.state = (lblc i).1)
    (hFanc : ∀ i, 1 ≤ i → i ≤ hc → ∀ j : Fin 3,
        ((j : ℕ) < foc i ↔ (if (j : ℕ) < foc i then some (clabc i (j + 1)) else none) ≠ none))
    -- child-content link:
    -- a STRUCTURAL commitment of the committed trace, supplied alongside `hStatec`/`hFanc`
    (hLinkc : ∀ i, 1 ≤ i → i ≤ hc → ComputeTable.childLinkComp (lblc i)
        (fun j : Fin 3 => if (j : ℕ) < foc i then some (clabc i (j + 1)) else none)) :
    ∀ i, 1 ≤ i → i ≤ hc →
      (∃ ex, ComputeTable.RAPcomp (lblc i).2.1 (lblc i).2.2.1 (lblc i).2.2.2 ex)
        ∧ (lblc i).2.2.1.state = (lblc i).1
        ∧ (∀ j : Fin 3, (j : ℕ) < foc i ↔
            (if (j : ℕ) < foc i then some (clabc i (j + 1)) else none) ≠ none)
        ∧ ComputeTable.childLinkComp (lblc i)
            (fun j : Fin 3 => if (j : ℕ) < foc i then some (clabc i (j + 1)) else none) := by
  intro i h1 h2
  obtain ⟨ex, hex⟩ := hAIRc i h1 h2
  exact ⟨row_computeAIR_gives_RAP _ _ _ ex hex, hStatec i h1 h2, hFanc i h1 h2, hLinkc i h1 h2⟩

/-- **`exported_memory_rows_give_hRm`.**  Per-row `(memoryAIR (K := K))` satisfaction plus the structural
    facts PRODUCE the exact per-row hypothesis `hRm` of `V_NockVMROM_forest`. -/
theorem exported_memory_rows_give_hRm
    (lblm : ℕ → MemoryTable.MState × MemoryTable.DTmem K) (clabm : ℕ → ℕ → MemoryTable.MState × MemoryTable.DTmem K)
    (fom : ℕ → ℕ) (hm : ℕ)
    (hAIRm : ∀ i, 1 ≤ i → i ≤ hm → ∃ g : K,
        ∀ c ∈ (Reified.memoryAIR (K := K)).constraints,
          c.expr.eval (Reified.memoryEnvFull (lblm i).2.1
            (MemoryTable.opSel (lblm i).2.2.st) (lblm i).2.2 g) = 0)
    (hStatem : ∀ i, 1 ≤ i → i ≤ hm → (lblm i).2.2.st = (lblm i).1)
    (hFanm : ∀ i, 1 ≤ i → i ≤ hm → ∀ j : Fin 2,
        ((j : ℕ) < fom i ↔ (if (j : ℕ) < fom i then some (clabm i (j + 1)) else none) ≠ none))
    -- child-content link:
    -- a STRUCTURAL commitment of the committed trace, supplied alongside `hStatem`/`hFanm`
    (hLinkm : ∀ i, 1 ≤ i → i ≤ hm → MemoryTable.childLinkMem (lblm i)
        (fun j : Fin 2 => if (j : ℕ) < fom i then some (clabm i (j + 1)) else none)) :
    ∀ i, 1 ≤ i → i ≤ hm →
      (∃ g, MemoryTable.RAPmem (lblm i).2.1 (lblm i).2.2 g)
        ∧ (lblm i).2.2.st = (lblm i).1
        ∧ (∀ j : Fin 2, (j : ℕ) < fom i ↔
            (if (j : ℕ) < fom i then some (clabm i (j + 1)) else none) ≠ none)
        ∧ MemoryTable.childLinkMem (lblm i)
            (fun j : Fin 2 => if (j : ℕ) < fom i then some (clabm i (j + 1)) else none) := by
  intro i h1 h2
  obtain ⟨g, hg⟩ := hAIRm i h1 h2
  exact ⟨row_memoryAIR_gives_RAP _ _ g hg, hStatem i h1 h2, hFanm i h1 h2, hLinkm i h1 h2⟩

/-- **`fullAIR_entails_forest` (the payoff bridge, forward direction).**  The FULL exported AIR —
    the row-local `computeAIR`/`(memoryAIR (K := K))` (satisfied per row) plus the structural walk data — ENTAILS
    the composed capstone `NockVM.V_NockVMROM_forest` (compute-chip soundness `≤ hc/|K| + ε_RLC`,
    multi-root memory-chip soundness `≤ hm/|K| + ε_RLC`, and the `Thm:IO_result` linking of the
    walks' own committed memory traffic).  The per-row `∃ ex/g RAP` hypotheses are DISCHARGED by the
    exported AIR (`exported_compute_rows_give_hRc`/`exported_memory_rows_give_hRm`); the tree-
    structural side conditions remain assumed, exactly as the capstone assumes them. -/
theorem fullAIR_entails_forest
    {p : ℕ} [CharP K p]
    {ncs : ℕ} (encc : (State × ComputeTable.DTcomp K) → (Fin ncs → K)) (hEncc : Function.Injective encc)
    (lblc : ℕ → State × ComputeTable.DTcomp K) (clabc : ℕ → ℕ → State × ComputeTable.DTcomp K) (foc : ℕ → ℕ)
    {hc : ℕ} (harityc : ∀ i, foc i ≤ 3)
    (qc qinvc : ℕ → K) (hqc : Walk.QGate foc qc qinvc 1 hc) (hwrapc : 1 + hc * 3 < p)
    (hfoc : ∀ i, 1 ≤ i → i ≤ hc → foc i = (ComputeTable.comp_stateSep (K := K)).fanout (lblc i).1)
    (hAIRc : ∀ i, 1 ≤ i → i ≤ hc → ∃ ex : ComputeTable.Extra K,
        ∀ c ∈ Reified.computeAIR.constraints,
          c.expr.eval (Reified.computeEnvFull (lblc i).2.1
            (ComputeTable.opSel (lblc i).2.2.1.state) (lblc i).2.2.1 (lblc i).2.2.2 ex) = 0)
    (hStatec : ∀ i, 1 ≤ i → i ≤ hc → (lblc i).2.2.1.state = (lblc i).1)
    (hFanc : ∀ i, 1 ≤ i → i ≤ hc → ∀ j : Fin 3,
        ((j : ℕ) < foc i ↔ (if (j : ℕ) < foc i then some (clabc i (j + 1)) else none) ≠ none))
    (hLinkc : ∀ i, 1 ≤ i → i ≤ hc → ComputeTable.childLinkComp (lblc i)
        (fun j : Fin 3 => if (j : ℕ) < foc i then some (clabc i (j + 1)) else none))
    {nms : ℕ} (encm : (MemoryTable.MState × MemoryTable.DTmem K) → (Fin nms → K)) (hEncm : Function.Injective encm)
    (lblm : ℕ → MemoryTable.MState × MemoryTable.DTmem K) (clabm : ℕ → ℕ → MemoryTable.MState × MemoryTable.DTmem K) (fom : ℕ → ℕ)
    {kroots_m hm : ℕ} (hkm : 1 ≤ kroots_m) (haritym : ∀ i, fom i ≤ 2)
    (qm qinvm : ℕ → K) (hqm : Walk.QGate fom qm qinvm kroots_m hm)
    (hwrapm : kroots_m + hm * 2 < p)
    (hfom : ∀ i, 1 ≤ i → i ≤ hm → fom i = (MemoryTable.mem_stateSep (K := K)).fanout (lblm i).1)
    (hAIRm : ∀ i, 1 ≤ i → i ≤ hm → ∃ g : K,
        ∀ c ∈ (Reified.memoryAIR (K := K)).constraints,
          c.expr.eval (Reified.memoryEnvFull (lblm i).2.1
            (MemoryTable.opSel (lblm i).2.2.st) (lblm i).2.2 g) = 0)
    (hStatem : ∀ i, 1 ≤ i → i ≤ hm → (lblm i).2.2.st = (lblm i).1)
    (hFanm : ∀ i, 1 ≤ i → i ≤ hm → ∀ j : Fin 2,
        ((j : ℕ) < fom i ↔ (if (j : ℕ) < fom i then some (clabm i (j + 1)) else none) ≠ none))
    (hLinkm : ∀ i, 1 ≤ i → i ≤ hm → MemoryTable.childLinkMem (lblm i)
        (fun j : Fin 2 => if (j : ℕ) < fom i then some (clabm i (j + 1)) else none))
    (lmb : K) (Ksz : ℕ) (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz (NockVM.reqRecs lblc hc lmb).length)
    (hKresp : (NockVM.respRecs lblm hm).length ≤ Ksz)
    (hreqnd : (NockVM.reqRecs lblc hc lmb).Nodup) (hrespnd : (NockVM.respRecs lblm hm).Nodup) :
    (((NockVM.walkBad (ComputeTable.comp_stateSep (K := K)) encc lblc clabc foc hc).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hc : ℚ) / (Fintype.card K : ℚ)
          + ((hc * (ncs - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    ∧ (((NockVM.walkBadForest (MemoryTable.mem_stateSep (K := K)) encm lblm clabm fom kroots_m hm).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hm : ℚ) / (Fintype.card K : ℚ)
          + ((hm * (nms - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    ∧ ((∃ (m : Fin (NockVM.respRecs lblm hm).length → ZMod p) (accP accM : ℕ → RatFunc (RatFunc K))
          (requests responses out_mem : RatFunc (RatFunc K)),
          (∀ j, m j ≠ 0)
          ∧ IO.ProgIOSat (fun i => SetEq.RLC (IO.listExt (NockVM.reqRecs lblc hc lmb) i)) accP requests
              (NockVM.reqRecs lblc hc lmb).length
          ∧ IO.MemIOSat (fun i => SetEq.RLC (IO.listExt (NockVM.respRecs lblm hm) i)) (IO.castμ m) accM
              responses out_mem (NockVM.respRecs lblm hm).length
          ∧ requests = responses ∧ out_mem = 0)
        ↔ IO.LIO Ksz (NockVM.reqRecs lblc hc lmb) (NockVM.respRecs lblm hm)) :=
  NockVM.V_NockVMROM_forest encc hEncc lblc clabc foc harityc qc qinvc hqc hwrapc hfoc
    (exported_compute_rows_give_hRc lblc clabc foc hc hAIRc hStatec hFanc hLinkc)
    encm hEncm lblm clabm fom hkm haritym qm qinvm hqm hwrapm hfom
    (exported_memory_rows_give_hRm lblm clabm fom hm hAIRm hStatem hFanm hLinkm)
    Ksz hKp hKreq hKresp hreqnd hrespnd

end Bridge

/-! ## 7. Tier A.2 — making the reified transition gates LOAD-BEARING

  Tier A proved the reified walk/IO/chaining gates TIGHT BICONDICTIONAL to
  `Walk.WalkSat`/`IO.ProgIOSat`/`IO.MemIOSat`, but `fullAIR_entails_forest` never referenced
  them (the `WalkSat` was baked inside `walkBad`'s acceptance predicate; the IO existential was
  characterized by `io_result_LIO` with no gate slot).  This section closes that gap: the walk
  bad-sets are re-expressed over the *challenge-instantiated reified gates* (`WalkGatesSat`), the
  IO existential is *supplied by* the reified IO gates, and the memory/compute chaining gates feed
  new cross-row output conjuncts — all via the `reified_*_sound` biconditionals, which are now
  genuinely part of the proof term of `fullAIR_entails_forest'`.

  Position-free (memoryless, positionless): every transfer is a biconditional over per-row / two-row
  gate evaluations — no pointers, no committed-line lookups, no ordering gate. -/

section LoadBearing

variable {K : Type*} [Field K]

/-- **`WalkGatesSat`** — the challenge-instantiated reified walk gates, i.e. the RHS of
    `reified_walk_sound`: the `.boundary` gates at row 1 and the `.transition` gates over rows
    `1..h−1`, each asserted to evaluate to zero.  This is the object the load-bearing bad-set
    filters on (replacing the baked-in `Walk.WalkSat`). -/
def WalkGatesSat (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (ln cnt acc : ℕ → K) (α seed ic : K) (h : ℕ) : Prop :=
  1 ≤ h
  ∧ walkLn1.eval (walkRowEnv cur chld' fo ln cnt acc α seed ic 1) = 0
  ∧ walkCount1.eval (walkRowEnv cur chld' fo ln cnt acc α seed ic 1) = 0
  ∧ walkAccInit.eval (walkRowEnv cur chld' fo ln cnt acc α seed ic 1) = 0
  ∧ (∀ i, 1 ≤ i → i < h →
        walkLnStep.eval (walkStep cur chld' fo ln cnt acc α seed ic i) = 0
      ∧ walkCountStep.eval (walkStep cur chld' fo ln cnt acc α seed ic i) = 0
      ∧ walkAccStep.eval (walkStep cur chld' fo ln cnt acc α seed ic i) = 0)

/-- The reified walk gates are satisfied **iff** the proven `Walk.WalkSat` holds — this is exactly
    `reified_walk_sound`, packaged so it can be plugged into the bad-set filter congruence.  This
    is THE lemma whose deletion breaks `walkBadReified_eq` (hence `fullAIR_entails_forest'`). -/
theorem walkGatesSat_iff_walkSat (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (ln cnt acc : ℕ → K) (α seed ic : K) (h : ℕ) :
    WalkGatesSat cur chld' fo ln cnt acc α seed ic h
      ↔ Walk.WalkSat cur chld' fo ln cnt acc α seed ic h := by
  unfold WalkGatesSat
  exact reified_walk_sound.symm

/-- Hosted census of the deployed (mask-form) walk: same ln/count gates, acc in
    `walkAccInitMasked` / `walkAccStepMasked`. -/
def WalkGatesSatMasked (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (ln cnt acc : ℕ → K) (α seed ic : K) (rm : ℕ → K) (h : ℕ) : Prop :=
  1 ≤ h
  ∧ walkLn1.eval (walkRowEnvMasked cur chld' fo ln cnt acc α seed ic rm 1) = 0
  ∧ walkCount1.eval (walkRowEnvMasked cur chld' fo ln cnt acc α seed ic rm 1) = 0
  ∧ walkAccInitMasked.eval (walkRowEnvMasked cur chld' fo ln cnt acc α seed ic rm 1) = 0
  ∧ (∀ i, 1 ≤ i → i < h →
        walkLnStep.eval (walkStepMasked cur chld' fo ln cnt acc α seed ic rm i) = 0
      ∧ walkCountStep.eval (walkStepMasked cur chld' fo ln cnt acc α seed ic rm i) = 0
      ∧ walkAccStepMasked.eval (walkStepMasked cur chld' fo ln cnt acc α seed ic rm i) = 0)

variable [Fintype K] [DecidableEq K]

/-- **`walkBadReified` (deliverable #1).**  The `walkBad` bad-challenge set, re-expressed so its
    acceptance predicate is the challenge-instantiated reified walk gates (`WalkGatesSat` at
    `(α,γ) = p` plus the terminal `walkOut = acc h = 0`) instead of the baked-in `Walk.WalkSat`.
    This makes the EXPORTED `walkAIR` the object the soundness bound counts. -/
noncomputable def walkBadReified {S DT : Type*} {n node_size : ℕ}
    {F : (S × DT) → (Fin n → Option (S × DT)) → Prop} (St : Walk.StateSep F)
    (enc : (S × DT) → (Fin node_size → K)) (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT)
    (fo : ℕ → ℕ) (h : ℕ) : Finset (K × K) :=
  Finset.univ.filter (fun p : K × K =>
    (∃ ln count acc : ℕ → K,
      WalkGatesSat (fun i => Walk.rlc p.2 (enc (lbl i))) (fun i l => Walk.rlc p.2 (enc (clab i l)))
          fo ln count acc p.1 (Walk.rlc p.2 (enc (lbl 1)) * p.1) p.1 h
      ∧ walkOut.eval (walkRowEnv (fun i => Walk.rlc p.2 (enc (lbl i)))
          (fun i l => Walk.rlc p.2 (enc (clab i l))) fo ln count acc p.1
          (Walk.rlc p.2 (enc (lbl 1)) * p.1) p.1 h) = 0)
    ∧ ¬ Walk.ReconGoal St lbl h)

/-- **`walkBadReified = walkBad`** — the reified-gate filter predicate equals the `WalkSat`
    filter predicate, pointwise, via `walkGatesSat_iff_walkSat` (= `reified_walk_sound`) on the
    recurrence part and `reified_walk_out_sound` on the terminal part. -/
theorem walkBadReified_eq {S DT : Type*} {n node_size : ℕ}
    {F : (S × DT) → (Fin n → Option (S × DT)) → Prop} (St : Walk.StateSep F)
    (enc : (S × DT) → (Fin node_size → K)) (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT)
    (fo : ℕ → ℕ) (h : ℕ) :
    walkBadReified St enc lbl clab fo h = NockVM.walkBad St enc lbl clab fo h := by
  unfold walkBadReified NockVM.walkBad
  apply Finset.filter_congr
  intro p _
  constructor
  · rintro ⟨⟨ln, count, acc, hg, hout⟩, hrec⟩
    exact ⟨⟨ln, count, acc,
      (walkGatesSat_iff_walkSat _ _ _ _ _ _ _ _ _ _).mp hg, reified_walk_out_sound.mp hout⟩, hrec⟩
  · rintro ⟨⟨ln, count, acc, hs, hah⟩, hrec⟩
    exact ⟨⟨ln, count, acc,
      (walkGatesSat_iff_walkSat _ _ _ _ _ _ _ _ _ _).mpr hs, reified_walk_out_sound.mpr hah⟩, hrec⟩

/-- **`walkBadReified_prob`.**  The Sprint-14 soundness bound `≤ h/|K| + ε_RLC`, now stated over
    the EXPORTED reified walk gates — obtained by rewriting `walkBad_prob` along
    `walkBadReified_eq`. -/
theorem walkBadReified_prob {S DT : Type*} {n node_size : ℕ}
    {F : (S × DT) → (Fin n → Option (S × DT)) → Prop} (St : Walk.StateSep F)
    (enc : (S × DT) → (Fin node_size → K)) (hEnc : Function.Injective enc)
    (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Walk.Sf fo h + 1 = h) (hvalid : Walk.BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)) :
    ((walkBadReified St enc lbl clab fo h).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (h : ℚ) / (Fintype.card K : ℚ)
          + ((h * (node_size - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ) := by
  rw [walkBadReified_eq]
  exact NockVM.walkBad_prob St enc hEnc lbl clab fo hSf hvalid harity hfo hFcommit

/-- **`walkBadForestReified` (deliverable #1, forest seed).**  The multi-root `walkBadForest`
    bad-set re-expressed over the reified walk gates (forest seed
    `Σ_{i≤kroots} RLC^γ(lblᵢ)·αⁱ`, initial count `α^kroots`). -/
noncomputable def walkBadForestReified {S DT : Type*} {n node_size : ℕ}
    {F : (S × DT) → (Fin n → Option (S × DT)) → Prop} (St : Walk.StateSep F)
    (enc : (S × DT) → (Fin node_size → K)) (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT)
    (fo : ℕ → ℕ) (kroots h : ℕ) : Finset (K × K) :=
  Finset.univ.filter (fun p : K × K =>
    (∃ ln count acc : ℕ → K,
      WalkGatesSat (fun i => Walk.rlc p.2 (enc (lbl i))) (fun i l => Walk.rlc p.2 (enc (clab i l)))
          fo ln count acc p.1 (∑ i ∈ Finset.Icc 1 kroots, Walk.rlc p.2 (enc (lbl i)) * p.1 ^ i)
          (p.1 ^ kroots) h
      ∧ walkOut.eval (walkRowEnv (fun i => Walk.rlc p.2 (enc (lbl i)))
          (fun i l => Walk.rlc p.2 (enc (clab i l))) fo ln count acc p.1
          (∑ i ∈ Finset.Icc 1 kroots, Walk.rlc p.2 (enc (lbl i)) * p.1 ^ i) (p.1 ^ kroots) h) = 0)
    ∧ ¬ Walk.ForestReconGoal St lbl kroots h)

/-- **`walkBadForestReified = walkBadForest`** (forest analogue of `walkBadReified_eq`). -/
theorem walkBadForestReified_eq {S DT : Type*} {n node_size : ℕ}
    {F : (S × DT) → (Fin n → Option (S × DT)) → Prop} (St : Walk.StateSep F)
    (enc : (S × DT) → (Fin node_size → K)) (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT)
    (fo : ℕ → ℕ) (kroots h : ℕ) :
    walkBadForestReified St enc lbl clab fo kroots h
      = NockVM.walkBadForest St enc lbl clab fo kroots h := by
  unfold walkBadForestReified NockVM.walkBadForest
  apply Finset.filter_congr
  intro p _
  constructor
  · rintro ⟨⟨ln, count, acc, hg, hout⟩, hrec⟩
    exact ⟨⟨ln, count, acc,
      (walkGatesSat_iff_walkSat _ _ _ _ _ _ _ _ _ _).mp hg, reified_walk_out_sound.mp hout⟩, hrec⟩
  · rintro ⟨⟨ln, count, acc, hs, hah⟩, hrec⟩
    exact ⟨⟨ln, count, acc,
      (walkGatesSat_iff_walkSat _ _ _ _ _ _ _ _ _ _).mpr hs, reified_walk_out_sound.mpr hah⟩, hrec⟩

/-- **`walkBadForestReified_prob`.**  Multi-root soundness bound over the exported reified gates. -/
theorem walkBadForestReified_prob {S DT : Type*} {n node_size : ℕ}
    {F : (S × DT) → (Fin n → Option (S × DT)) → Prop} (St : Walk.StateSep F)
    (enc : (S × DT) → (Fin node_size → K)) (hEnc : Function.Injective enc)
    (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {kroots h : ℕ} (hk : 1 ≤ kroots) (hSf : kroots + Walk.Sf fo h = h)
    (hvalid : Walk.BFSValidF kroots fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)) :
    ((walkBadForestReified St enc lbl clab fo kroots h).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (h : ℚ) / (Fintype.card K : ℚ)
          + ((h * (node_size - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ) := by
  rw [walkBadForestReified_eq]
  exact NockVM.walkBadForest_prob St enc hEnc lbl clab fo hk hSf hvalid harity hfo hFcommit

/-- **`fullAIR_entails_forest'` (the UPGRADED payoff bridge — Tier A.2).**  Supersedes
    `fullAIR_entails_forest` by making the reified transition gates genuinely LOAD-BEARING.  As
    before, per-row `computeAIR`/`(memoryAIR (K := K))` satisfaction (`hAIRc`/`hAIRm`) discharges the capstone's
    row-local RAP hypotheses.  Additionally:

    * **(1)/(2)** are stated over `walkBadReified`/`walkBadForestReified` — the bad-sets whose
      acceptance predicate IS the challenge-instantiated exported walk gates; the equality to
      `walkBad`/`walkBadForest` (hence the bound) flows through `walkBadReified_eq` /
      `walkBadForestReified_eq`, i.e. through `reified_walk_sound`.
    * **(3)** keeps the full `io_result_LIO` biconditional UNCHANGED and additionally *realizes*
      its LHS existential: the `ProgIOSat`/`MemIOSat` witnesses are PRODUCED from satisfaction of
      the exported `ioProgAIR`/`ioMemAIR` gates (`hioP*`/`hioM*`) via `exported_ioProg_gives_ProgIOSat`
      / `exported_ioMem_gives_MemIOSat` (= `reified_io_prog_sound`/`reified_io_mem_sound`).  The
      IO-consistency (`requests = responses`, `out_mem = 0`, `m ≠ 0`) is assumed exactly as the
      capstone certifies it.
    * **(4)** the memory LogUp accumulator chains: `icur(i) = ipre(i+1)`, DERIVED from the
      `memoryAIRchained` transition gate via `reified_icur_chain_sound`.
    * **(5)** the compute line-nonce chains: `ln(i) = ln_prev(i+1)`, DERIVED from the
      `computeAIRchained` transition gate via `reified_ln_chain_sound`.

    The tree-STRUCTURAL side conditions (`Sf`-tiling, BFS-validity, arity, state/fanout matching,
    encoder injectivity, IO range/`Nodup`) remain assumed exactly as the capstone assumes them —
    they are not local polynomial gates.  Honest `+ ε_RLC` retained; no conjunct weakened. -/
theorem fullAIR_entails_forest'
    {p : ℕ} [CharP K p]
    {ncs : ℕ} (encc : (State × ComputeTable.DTcomp K) → (Fin ncs → K)) (hEncc : Function.Injective encc)
    (lblc : ℕ → State × ComputeTable.DTcomp K) (clabc : ℕ → ℕ → State × ComputeTable.DTcomp K) (foc : ℕ → ℕ)
    {hc : ℕ} (harityc : ∀ i, foc i ≤ 3)
    (qc qinvc : ℕ → K) (hqc : Walk.QGate foc qc qinvc 1 hc) (hwrapc : 1 + hc * 3 < p)
    (hfoc : ∀ i, 1 ≤ i → i ≤ hc → foc i = (ComputeTable.comp_stateSep (K := K)).fanout (lblc i).1)
    (hAIRc : ∀ i, 1 ≤ i → i ≤ hc → ∃ ex : ComputeTable.Extra K,
        ∀ c ∈ Reified.computeAIR.constraints,
          c.expr.eval (Reified.computeEnvFull (lblc i).2.1
            (ComputeTable.opSel (lblc i).2.2.1.state) (lblc i).2.2.1 (lblc i).2.2.2 ex) = 0)
    (hStatec : ∀ i, 1 ≤ i → i ≤ hc → (lblc i).2.2.1.state = (lblc i).1)
    (hFanc : ∀ i, 1 ≤ i → i ≤ hc → ∀ j : Fin 3,
        ((j : ℕ) < foc i ↔ (if (j : ℕ) < foc i then some (clabc i (j + 1)) else none) ≠ none))
    (hLinkc : ∀ i, 1 ≤ i → i ≤ hc → ComputeTable.childLinkComp (lblc i)
        (fun j : Fin 3 => if (j : ℕ) < foc i then some (clabc i (j + 1)) else none))
    {nms : ℕ} (encm : (MemoryTable.MState × MemoryTable.DTmem K) → (Fin nms → K)) (hEncm : Function.Injective encm)
    (lblm : ℕ → MemoryTable.MState × MemoryTable.DTmem K) (clabm : ℕ → ℕ → MemoryTable.MState × MemoryTable.DTmem K) (fom : ℕ → ℕ)
    {kroots_m hm : ℕ} (hkm : 1 ≤ kroots_m) (haritym : ∀ i, fom i ≤ 2)
    (qm qinvm : ℕ → K) (hqm : Walk.QGate fom qm qinvm kroots_m hm)
    (hwrapm : kroots_m + hm * 2 < p)
    (hfom : ∀ i, 1 ≤ i → i ≤ hm → fom i = (MemoryTable.mem_stateSep (K := K)).fanout (lblm i).1)
    (hAIRm : ∀ i, 1 ≤ i → i ≤ hm → ∃ g : K,
        ∀ c ∈ (Reified.memoryAIR (K := K)).constraints,
          c.expr.eval (Reified.memoryEnvFull (lblm i).2.1
            (MemoryTable.opSel (lblm i).2.2.st) (lblm i).2.2 g) = 0)
    (hStatem : ∀ i, 1 ≤ i → i ≤ hm → (lblm i).2.2.st = (lblm i).1)
    (hFanm : ∀ i, 1 ≤ i → i ≤ hm → ∀ j : Fin 2,
        ((j : ℕ) < fom i ↔ (if (j : ℕ) < fom i then some (clabm i (j + 1)) else none) ≠ none))
    (hLinkm : ∀ i, 1 ≤ i → i ≤ hm → MemoryTable.childLinkMem (lblm i)
        (fun j : Fin 2 => if (j : ℕ) < fom i then some (clabm i (j + 1)) else none))
    (lmb : K) (Ksz : ℕ) (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz (NockVM.reqRecs lblc hc lmb).length)
    (hKresp : (NockVM.respRecs lblm hm).length ≤ Ksz)
    (hreqnd : (NockVM.reqRecs lblc hc lmb).Nodup) (hrespnd : (NockVM.respRecs lblm hm).Nodup)
    -- exported IO-gate satisfaction: the reified `ioProgAIR`/`ioMemAIR` supply the accumulators
    (accP accM : ℕ → RatFunc (RatFunc K)) (requests responses out_mem : RatFunc (RatFunc K))
    (m : Fin (NockVM.respRecs lblm hm).length → ZMod p)
    (hmne : ∀ j, m j ≠ 0) (hrr : requests = responses) (hout : out_mem = 0)
    (hioPinit : ioProgInit.eval
        (ioProgRowEnv (fun i => SetEq.RLC (IO.listExt (NockVM.reqRecs lblc hc lmb) i)) accP requests 0) = 0)
    (hioPstep : ∀ i, i < (NockVM.reqRecs lblc hc lmb).length →
        ioProgStep.eval (twoRow
          (ioProgRowEnv (fun i => SetEq.RLC (IO.listExt (NockVM.reqRecs lblc hc lmb) i)) accP requests i)
          (ioProgRowEnv (fun i => SetEq.RLC (IO.listExt (NockVM.reqRecs lblc hc lmb) i)) accP requests (i + 1))) = 0)
    (hioPterm : ioProgTerm.eval
        (ioProgRowEnv (fun i => SetEq.RLC (IO.listExt (NockVM.reqRecs lblc hc lmb) i)) accP requests
          (NockVM.reqRecs lblc hc lmb).length) = 0)
    (hioMinit : ioMemInit.eval
        (ioMemRowEnv (fun i => SetEq.RLC (IO.listExt (NockVM.respRecs lblm hm) i)) (IO.castμ m) accM
          responses out_mem 0) = 0)
    (hioMstep : ∀ i, i < (NockVM.respRecs lblm hm).length →
        ioMemStep.eval (twoRow
          (ioMemRowEnv (fun i => SetEq.RLC (IO.listExt (NockVM.respRecs lblm hm) i)) (IO.castμ m) accM responses out_mem i)
          (ioMemRowEnv (fun i => SetEq.RLC (IO.listExt (NockVM.respRecs lblm hm) i)) (IO.castμ m) accM responses out_mem (i + 1))) = 0)
    (hioMterm : ioMemTerm.eval
        (ioMemRowEnv (fun i => SetEq.RLC (IO.listExt (NockVM.respRecs lblm hm) i)) (IO.castμ m) accM
          responses out_mem (NockVM.respRecs lblm hm).length) = 0)
    -- exported memory chaining gate (`memoryAIRchained`'s transition, cross-row)
    (minpm : MemoryTable.Inputs K)
    (hchainm : ∀ i, 1 ≤ i → i < hm →
        icurChainExpr.eval (twoRow
          (Reified.memoryEnvFull minpm (MemoryTable.opSel (lblm i).2.2.st) (lblm i).2.2 0)
          (Reified.memoryEnvFull minpm (MemoryTable.opSel (lblm (i + 1)).2.2.st) (lblm (i + 1)).2.2 0)) = 0)
    -- exported compute line-nonce chaining gate (`computeAIRchained`'s transition, cross-row)
    (inpc : ComputeTable.Inputs K) (exc : ℕ → ComputeTable.Extra K)
    (hlnc : ∀ i, 1 ≤ i → i < hc →
        lnChainExpr.eval (twoRow
          (Reified.computeEnvFull inpc (ComputeTable.opSel (lblc i).2.2.1.state) (lblc i).2.2.1 (lblc i).2.2.2 (exc i))
          (Reified.computeEnvFull inpc (ComputeTable.opSel (lblc (i + 1)).2.2.1.state) (lblc (i + 1)).2.2.1 (lblc (i + 1)).2.2.2 (exc (i + 1)))) = 0) :
    -- (1) compute chip soundness, over the EXPORTED reified walk gates
    (((walkBadReified (ComputeTable.comp_stateSep (K := K)) encc lblc clabc foc hc).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hc : ℚ) / (Fintype.card K : ℚ)
          + ((hc * (ncs - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    -- (2) memory chip soundness (multi-root forest), over the EXPORTED reified walk gates
    ∧ (((walkBadForestReified (MemoryTable.mem_stateSep (K := K)) encm lblm clabm fom kroots_m hm).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hm : ℚ) / (Fintype.card K : ℚ)
          + ((hm * (nms - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    -- (3) IO linking: the `io_result_LIO` biconditional AND its LHS existential, the latter
    --     SUPPLIED by the exported IO gates
    ∧ (((∃ (m : Fin (NockVM.respRecs lblm hm).length → ZMod p) (accP accM : ℕ → RatFunc (RatFunc K))
          (requests responses out_mem : RatFunc (RatFunc K)),
          (∀ j, m j ≠ 0)
          ∧ IO.ProgIOSat (fun i => SetEq.RLC (IO.listExt (NockVM.reqRecs lblc hc lmb) i)) accP requests
              (NockVM.reqRecs lblc hc lmb).length
          ∧ IO.MemIOSat (fun i => SetEq.RLC (IO.listExt (NockVM.respRecs lblm hm) i)) (IO.castμ m) accM
              responses out_mem (NockVM.respRecs lblm hm).length
          ∧ requests = responses ∧ out_mem = 0)
        ↔ IO.LIO Ksz (NockVM.reqRecs lblc hc lmb) (NockVM.respRecs lblm hm))
      ∧ (∃ (m : Fin (NockVM.respRecs lblm hm).length → ZMod p) (accP accM : ℕ → RatFunc (RatFunc K))
          (requests responses out_mem : RatFunc (RatFunc K)),
          (∀ j, m j ≠ 0)
          ∧ IO.ProgIOSat (fun i => SetEq.RLC (IO.listExt (NockVM.reqRecs lblc hc lmb) i)) accP requests
              (NockVM.reqRecs lblc hc lmb).length
          ∧ IO.MemIOSat (fun i => SetEq.RLC (IO.listExt (NockVM.respRecs lblm hm) i)) (IO.castμ m) accM
              responses out_mem (NockVM.respRecs lblm hm).length
          ∧ requests = responses ∧ out_mem = 0))
    -- (4) memory LogUp accumulator chaining, DERIVED from the memoryAIRchained transition gate
    ∧ (∀ i, 1 ≤ i → i < hm → (lblm i).2.2.icur = (lblm (i + 1)).2.2.ipre)
    -- (5) compute line-nonce chaining, DERIVED from the computeAIRchained transition gate
    ∧ (∀ i, 1 ≤ i → i < hc → (lblc i).2.2.1.ln = (lblc (i + 1)).2.2.1.ln_prev) := by
  obtain ⟨hb1, hb2, hbic⟩ :=
    NockVM.V_NockVMROM_forest encc hEncc lblc clabc foc harityc qc qinvc hqc hwrapc hfoc
      (exported_compute_rows_give_hRc lblc clabc foc hc hAIRc hStatec hFanc hLinkc)
      encm hEncm lblm clabm fom hkm haritym qm qinvm hqm hwrapm hfom
      (exported_memory_rows_give_hRm lblm clabm fom hm hAIRm hStatem hFanm hLinkm)
      Ksz hKp hKreq hKresp hreqnd hrespnd
  refine ⟨?_, ?_, ⟨hbic, ?_⟩, ?_, ?_⟩
  · -- (1): reified walk gates ARE the counted object (via reified_walk_sound / walkBadReified_eq)
    rw [walkBadReified_eq]; exact hb1
  · -- (2): forest, likewise
    rw [walkBadForestReified_eq]; exact hb2
  · -- (3): the IO existential, SUPPLIED by the exported IO gates via reified_io_*_sound
    exact ⟨m, accP, accM, requests, responses, out_mem, hmne,
      exported_ioProg_gives_ProgIOSat
        (fun i => SetEq.RLC (IO.listExt (NockVM.reqRecs lblc hc lmb) i)) accP requests
        (NockVM.reqRecs lblc hc lmb).length hioPinit hioPstep hioPterm,
      exported_ioMem_gives_MemIOSat
        (fun i => SetEq.RLC (IO.listExt (NockVM.respRecs lblm hm) i)) (IO.castμ m) accM responses out_mem
        (NockVM.respRecs lblm hm).length hioMinit hioMstep hioMterm,
      hrr, hout⟩
  · -- (4): memory chaining, DERIVED from the transition gate via reified_icur_chain_sound
    intro i h1 h2
    exact (reified_icur_chain_sound minpm (MemoryTable.opSel (lblm i).2.2.st)
      (MemoryTable.opSel (lblm (i + 1)).2.2.st) (lblm i).2.2 (lblm (i + 1)).2.2 0 0).mp
      (hchainm i h1 h2)
  · -- (5): compute line-nonce chaining, DERIVED via reified_ln_chain_sound
    intro i h1 h2
    exact (reified_ln_chain_sound inpc inpc (ComputeTable.opSel (lblc i).2.2.1.state)
      (ComputeTable.opSel (lblc (i + 1)).2.2.1.state) (lblc i).2.2.1 (lblc (i + 1)).2.2.1
      (lblc i).2.2.2 (lblc (i + 1)).2.2.2 (exc i) (exc (i + 1))).mp (hlnc i h1 h2)

end LoadBearing

-- Must be exactly
-- `[propext, Classical.choice, Quot.sound]` (NO `Field.goldilocks_prime`, NO `sorryAx`).
#print axioms reified_icur_chain_sound
#print axioms memIpreInit_sound
#print axioms memIcurTerm_sound
#print axioms memEndpointGates_sound
#print axioms reified_walk_sound
#print axioms reified_io_prog_sound
#print axioms reified_io_mem_sound
#print axioms exported_compute_rows_give_hRc
#print axioms exported_memory_rows_give_hRm
#print axioms fullAIR_entails_forest
-- Tier A.2 — the load-bearing upgrade.
#print axioms reified_ln_chain_sound
#print axioms exported_ioProg_gives_ProgIOSat
#print axioms exported_ioMem_gives_MemIOSat
#print axioms walkBadReified_prob
#print axioms walkBadForestReified_prob
#print axioms fullAIR_entails_forest'

end Trans

end Reified
end Nock
