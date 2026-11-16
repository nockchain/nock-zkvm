import Mathlib.Algebra.MvPolynomial.CommRing
import Nock.Framework.Separation
import Nock.Framework.Traversal
import Nock.NockVM
import Nock.AIR
import Nock.IO
import Nock.Walk

namespace Nock.Framework

open scoped Polynomial
open Nock.Walk Nock.ComputeTable Nock.MemoryTable

/-! ## INSTANCE: Nock is `(Fcomp, Fmem)`-traversable -/

/-- **INSTANCE (`Def:traversable`).**
    The NockVM compute and memory languages are `(Fcomp, Fmem)`-traversable.  Both traversal
    bijections are the identity onto a single-factor product (`k_comp = k_mem = 1`): the compute
    language `L_Lang^comp` **is** the recursively-verifiable-tree language `L_RVT^{Fcomp,3}`, and
    likewise the memory language is `L_RVT^{Fmem,2}` — this is exactly the paper's observation
 that it suffices to build a verifiable RAP for `L_RVT`, since it is *isomorphic*
    to proving the execution/memory traces valid.  That the Nock verifiers `V_comp`/`V_mem` recognise
    exactly these RVT-tree sets is `Thm:comp_38`/`Thm:mem_38` (`comp_stateSep`/`mem_stateSep`) composed with `Walk_IOP_final` — proved elsewhere; here the traversal
    bijection over those recognised languages is the identity.  Fully proved, axiom-clean. -/
noncomputable def nock_traversable (K : Type*) [Field K] :
    Traversable
      (LTc := State × DTcomp K) (nc := 3) (kc := 1)
      (LTm := MState × DTmem K) (nm := 2) (km := 1)
      {t : NTree (State × DTcomp K) // RVT (Fcomp (K := K)) t}
      {t : NTree (MState × DTmem K) // RVT (Fmem (K := K)) t}
      (fun _ => Fcomp (K := K))
      (fun _ => Fmem (K := K)) where
  φcomp := (Equiv.piUnique (fun _ : Fin 1 => {t : NTree (State × DTcomp K) // RVT (Fcomp (K := K)) t})).symm
  φmem := (Equiv.piUnique (fun _ : Fin 1 => {t : NTree (MState × DTmem K) // RVT (Fmem (K := K)) t})).symm

/-! ## INSTANCE: the Nock compute-table opcode selector is one-hot  (Def:one-hot) -/

/-- The 11 compute-table opcode selectors as an index `Fin 11 → State` (`OP_0..OP_9` and `cons`;
    `N_OP = 11` includes the implicit `cons`, whose selector participates in `SV3`). -/
def sfin : Fin 11 → State :=
  ![State.s0, State.s1, State.s2, State.s3, State.s4, State.s5,
    State.s6, State.s7, State.s8, State.s9, State.cons]

/-- **Opcode one-hot (Def:one-hot cond. 1).**  The compute-table opcode selector
    vector `opSel st` satisfies the paper's two booleanity/one-hot constraints for the active state:
    every selector is `0/1` and they sum to `1`.  Reuses `opSel_boolean`/`opSel_oneHot`. -/
theorem nock_opcode_oneHot (K : Type*) [Field K] (st : State) :
    (∀ j : Fin 11, opSel (K := K) st (sfin j) * (1 - opSel st (sfin j)) = 0)
      ∧ (∑ j : Fin 11, opSel (K := K) st (sfin j)) = 1 := by
  refine ⟨fun j => opSel_boolean (K := K) st (sfin j), ?_⟩
  have h := opSel_oneHot (K := K) st
  simp only [sum09] at h
  simp only [sfin, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  linear_combination h

/-- **`regs` for NockVM — memory records requested per opcode**.
    The number of non-zero records among the three `mr1/mr2/mr3` that `ComputeTable.memBlk` fixes
    for the opcode's state.  Record `mr1` always verifies the opening of the formula
, so every opcode requests `≥ 1` record and `OP_IO = OP`. -/
def recordCount : State → ℕ
  | .s0 => 2 | .s1 => 1 | .s2 => 2 | .s3 => 1 | .s4 => 1 | .s5 => 2
  | .s6 => 3 | .s7 => 2 | .s8 => 2 | .s9 => 3 | .cons => 1

theorem recordCount_pos (s : State) : 1 ≤ recordCount s := by cases s <;> decide

theorem recordCount_le (s : State) : recordCount s ≤ Nock.NockVM.mem_record_arity := by
  cases s <;> decide

/-- `encRec` of the zero record is the zero vector. -/
theorem encRec_zero (K : Type*) [Field K] (c : Fin 9) :
    Nock.NockVM.encRec (MemRec.zero : MemRec K) c = 0 := by
  fin_cases c <;> simp [Nock.NockVM.encRec, MemRec.zero]

/-- **`memBlk` forces `mr2 = 0` for opcodes requesting `≤ 1` record**. -/
theorem memBlk_mr2_zero (K : Type*) [Field K] (inp : ComputeTable.Inputs K)
    (pub : ComputeTable.Pub K) (dec : ComputeTable.Dec K)
    (h : ComputeTable.memBlk inp pub dec) (hle : recordCount pub.state ≤ 1) :
    pub.mr2 = MemRec.zero := by
  cases hs : pub.state <;> simp_all [ComputeTable.memBlk, recordCount]

/-- **`memBlk` forces `mr3 = 0` for opcodes requesting `≤ 2` records**. -/
theorem memBlk_mr3_zero (K : Type*) [Field K] (inp : ComputeTable.Inputs K)
    (pub : ComputeTable.Pub K) (dec : ComputeTable.Dec K)
    (h : ComputeTable.memBlk inp pub dec) (hle : recordCount pub.state ≤ 2) :
    pub.mr3 = MemRec.zero := by
  cases hs : pub.state <;> simp_all [ComputeTable.memBlk, recordCount]

/-- **INSTANCE (`Def:one-hot`).**  For a genuine compute
    trace — RAP inputs `inp` and per-row public+decomposition columns `rows i = (pub, dec)`, each
    satisfying the memory-record block `ComputeTable.memBlk` — the NockVM compute table is *opcode
    and memory one-hot* of size `N_OP = 11` (`OP_0..OP_9`, `cons`) and arity `M_OP = 3`
    (`mem_record_arity`) over `N_mem = 9` (`encRec`, form R):
    * cond. 1 (booleanity / one-hot): `opSel_boolean` / `opSel_oneHot`;
    * cond. 3 (`regs ≤ M_OP`): `recordCount_le`;
    * cond. 4 `io_zero`: `OP_IO = OP` — every opcode opens its formula via `mr1`
 — so `∑_{j∈OP_IO} x_prog(i,·) = 1 ≠ 0`; the hypothesis is unsatisfiable;
    * cond. 4 `regs_zero_pad`: from `memBlk` (`memBlk_mr2_zero`/`memBlk_mr3_zero`),
      the records beyond `regs = recordCount(state)` are `MemRec.zero`, encoded as `𝟎`;
    * cond. 5 `io_mem_subset`: **carried, see FINDING.** `x_mem`/`IO_mem` are
      memory-table objects, and the compute table does not itself verify records;
      this compute-side selector instance sets `h_R = 0`, so `IO_mem ⊆ x_mem` holds with no verified
      IO record — the substantive check lives in `RAP_mem`/`Thm:IO_result`, not modelled here. -/
noncomputable def nock_opcodeMemOneHot (K : Type*) [Field K] {h1 : ℕ}
    (inp : ComputeTable.Inputs K) (rows : Fin h1 → ComputeTable.Pub K × ComputeTable.Dec K)
    (hmem : ∀ i, ComputeTable.memBlk inp (rows i).1 (rows i).2) :
    OpcodeMemOneHot K where
  NOP := 11
  MOP := 3                              -- `= Nock.NockVM.mem_record_arity`
  Nmem := 9
  h1 := h1
  h2 := h1
  xprog := fun i j => ComputeTable.opSel (rows i).1.state (sfin j)
  IOprog := fun i k => Nock.NockVM.encRec
    (if k = 0 then (rows i).1.mr1 else if k = 1 then (rows i).1.mr2 else (rows i).1.mr3)
  xmem := fun _ _ => 0
  opIO := Finset.univ
  regs := fun j => recordCount (sfin j)
  hR := 0
  IOmem := fun r => r.elim0
  boolean := fun i j => opSel_boolean (K := K) (rows i).1.state (sfin j)
  oneHot := fun i => (nock_opcode_oneHot K (rows i).1.state).2
  regs_le := by intro j _; exact recordCount_le (sfin j)
  io_zero := by
    intro i hsum
    have h1eq := (nock_opcode_oneHot K (rows i).1.state).2
    exact absurd (hsum.symm.trans h1eq) zero_ne_one
  regs_zero_pad := by
    intro i j _ hx1 k hk c
    have hstate : sfin j = (rows i).1.state := by
      by_contra hne
      simp only [ComputeTable.opSel] at hx1
      rw [if_neg hne] at hx1
      exact one_ne_zero hx1.symm
    have hk' : recordCount (rows i).1.state ≤ (k : ℕ) := by rw [← hstate]; exact hk
    have hpos := recordCount_pos (rows i).1.state
    fin_cases k
    · have hk0 : recordCount (rows i).1.state ≤ 0 := by simpa using hk'
      omega
    · have hz := memBlk_mr2_zero K inp (rows i).1 (rows i).2 (hmem i) (by simpa using hk')
      simp [hz, encRec_zero]
    · have hz := memBlk_mr3_zero K inp (rows i).1 (rows i).2 (hmem i) (by simpa using hk')
      simp [hz, encRec_zero]
  hR_le := Nat.zero_le _
  io_mem_subset := fun r => r.elim0

/-! ## AIR → generic-`RAP` reification

  The generic `RAP` above stores its constraints as `MvPolynomial (Fin w × ℕ) F` — the paper's
  symbolic-variable form `C_i ∈ 𝔽^{≤d}[Y]` with `Y_{i,j}` indexed by `I ⊆ [w] × {0,…,2^h−1}`
.  The concrete NockVM tables, however, are produced as a **deep-embedded**
  AIR (`Nock.Reified.AIR`, `Nock.Reified.Expr`) whose constraints are evaluated pointwise through
  an `Env` (`Nock.Reified.Expr.eval`).  This section supplies the missing *translation between the
  two representations* and proves it exact:

  * `exprToMv`  — reify a `Reified.Expr` into `MvPolynomial (Fin w × ℕ) F`, mapping the current-row
    column `i` to `Y_{i,0}` and the next-row column `i` to `Y_{i,1}` (the paper's *adjacent trace
    rows*, `I = [w]×{0,1}`), and the verifier randomness / public inputs to field
    constants (a *randomized* AIR: after the verifier fixes its coins the constraints become
    concrete polynomials in the trace).
  * `airToRAP` — assemble a `Reified.AIR` into a `Framework.RAP` with exactly this `I` and the
    per-constraint reified polynomials.
  * `airToRAP_satisfies_iff` — **the key correspondence**: a trace of univariate
    polynomials `P` satisfies the reified RAP iff every deep-embedded constraint `Expr` evaluates to
    zero at every trace-domain point `x ∈ H`, reading `P` at `x` (current row) and `ω·x` (next row).
    This is exactly the paper's assignment rule `Y_{i,j} ↦ P_i(ω^j·X)`.

-/

namespace Reify

open scoped Polynomial

variable {F : Type*} [Field F]

/-- **Reify a `Reified.Expr` into the generic RAP symbolic-polynomial form.**
    Current-row column `i` ↦ `Y_{i,0} = X (⟨i⟩,0)`; next-row column `i` ↦ `Y_{i,1} = X (⟨i⟩,1)`
    (the paper's adjacent-row index set).  Verifier challenges and public inputs are
    substituted by their (already-fixed) field constants — the "randomized" in RAP.
    Out-of-range columns (`i ≥ w`) reify to `0`, matching `Reified.Env` (which reads `0` there). -/
noncomputable def exprToMv {w : ℕ} (chalVal pubVal : ℕ → F) :
    Reified.Expr → MvPolynomial (Fin w × ℕ) F
  | .Var .traceCur i  => if h : i < w then MvPolynomial.X (⟨i, h⟩, 0) else 0
  | .Var .traceNext i => if h : i < w then MvPolynomial.X (⟨i, h⟩, 1) else 0
  | .Var .challenge i => MvPolynomial.C (chalVal i)
  | .Var .publicVal i => MvPolynomial.C (pubVal i)
  | .Const c          => MvPolynomial.C (c : F)
  | .Add a b          => exprToMv chalVal pubVal a + exprToMv chalVal pubVal b
  | .Sub a b          => exprToMv chalVal pubVal a - exprToMv chalVal pubVal b
  | .Mul a b          => exprToMv chalVal pubVal a * exprToMv chalVal pubVal b
  | .Neg a            => - exprToMv chalVal pubVal a
  | .Pow e n          => (exprToMv chalVal pubVal e) ^ n

/-- The `Reified.Env` induced by a trace `P` of univariate polynomials at trace-domain point `x`:
    current row reads `P_i(x)`, next row reads `P_i(ω·x)`, challenges/public fixed. -/
noncomputable def envOfTrace {w : ℕ} (P : Fin w → F[X]) (ω x : F) (chalVal pubVal : ℕ → F) :
    Reified.Env F where
  trace     := fun i => if h : i < w then (P ⟨i, h⟩).eval x else 0
  traceNext := fun i => if h : i < w then (P ⟨i, h⟩).eval (ω * x) else 0
  chal      := chalVal
  pub       := pubVal

/-- **Faithfulness of the reification (the crux).**  Evaluating the reified multivariate polynomial
    under the assignment `Y_{i,j} ↦ P_i(ω^j·x)` reproduces the deep-embedded `Expr.eval` under the
    induced environment.  Structural induction on the expression. -/
theorem eval_exprToMv {w : ℕ} (P : Fin w → F[X]) (ω x : F) (chalVal pubVal : ℕ → F)
    (e : Reified.Expr) :
    MvPolynomial.eval (fun q : Fin w × ℕ => (P q.1).eval (ω ^ (q.2 : ℕ) * x))
        (exprToMv chalVal pubVal e)
      = e.eval (envOfTrace P ω x chalVal pubVal) := by
  induction e with
  | Var kind i =>
    cases kind
    · -- current row
      simp only [exprToMv, Reified.Expr.eval, envOfTrace]
      by_cases h : i < w
      · simp [h, MvPolynomial.eval_X, pow_zero, one_mul]
      · simp [h]
    · -- next row
      simp only [exprToMv, Reified.Expr.eval, envOfTrace]
      by_cases h : i < w
      · simp [h, MvPolynomial.eval_X, pow_one]
      · simp [h]
    · -- challenge
      simp [exprToMv, Reified.Expr.eval, envOfTrace, MvPolynomial.eval_C]
    · -- public
      simp [exprToMv, Reified.Expr.eval, envOfTrace, MvPolynomial.eval_C]
  | Const c => simp [exprToMv, Reified.Expr.eval]
  | Add a b iha ihb => simp only [exprToMv, Reified.Expr.eval, map_add, iha, ihb]
  | Sub a b iha ihb => simp only [exprToMv, Reified.Expr.eval, map_sub, iha, ihb]
  | Mul a b iha ihb => simp only [exprToMv, Reified.Expr.eval, map_mul, iha, ihb]
  | Neg a iha => simp only [exprToMv, Reified.Expr.eval, map_neg, iha]
  | Pow e n ihe => simp only [exprToMv, Reified.Expr.eval, map_pow, ihe]

/-- `exprToMv` only uses the symbolic variables `I = [w] × {0,1}` — the paper's adjacent-trace-row
    index set.  Needed for the `RAP.C_vars` field. -/
theorem exprToMv_vars {w : ℕ} (chalVal pubVal : ℕ → F) (e : Reified.Expr) :
    (exprToMv (w := w) chalVal pubVal e).vars ⊆ Finset.univ ×ˢ ({0, 1} : Finset ℕ) := by
  induction e with
  | Var kind i =>
    cases kind
    · simp only [exprToMv]
      by_cases h : i < w
      · rw [dif_pos h, MvPolynomial.vars_X, Finset.singleton_subset_iff, Finset.mem_product]
        exact ⟨Finset.mem_univ _, by simp⟩
      · rw [dif_neg h]; simp
    · simp only [exprToMv]
      by_cases h : i < w
      · rw [dif_pos h, MvPolynomial.vars_X, Finset.singleton_subset_iff, Finset.mem_product]
        exact ⟨Finset.mem_univ _, by simp⟩
      · rw [dif_neg h]; simp
    · simp [exprToMv, MvPolynomial.vars_C]
    · simp [exprToMv, MvPolynomial.vars_C]
  | Const c => simp only [exprToMv, MvPolynomial.vars_C]; exact Finset.empty_subset _
  | Add a b iha ihb =>
    exact (MvPolynomial.vars_add_subset _ _).trans (Finset.union_subset iha ihb)
  | Sub a b iha ihb =>
    simp only [exprToMv, sub_eq_add_neg]
    refine (MvPolynomial.vars_add_subset _ _).trans (Finset.union_subset iha ?_)
    rw [MvPolynomial.vars_neg]; exact ihb
  | Mul a b iha ihb =>
    exact (MvPolynomial.vars_mul _ _).trans (Finset.union_subset iha ihb)
  | Neg a iha => rw [exprToMv, MvPolynomial.vars_neg]; exact iha
  | Pow e n ihe =>
    simp only [exprToMv]
    have hpow : ((exprToMv (w := w) chalVal pubVal e) ^ n).vars
        ⊆ (exprToMv (w := w) chalVal pubVal e).vars := by
      induction n with
      | zero => rw [pow_zero, MvPolynomial.vars_one]; exact Finset.empty_subset _
      | succ k ihk =>
        rw [pow_succ]
        exact (MvPolynomial.vars_mul _ _).trans (Finset.union_subset ihk (Finset.Subset.refl _))
    exact hpow.trans ihe

/-- Evaluating an `aeval` into `F[X]` then at a point `x` equals the multivariate evaluation at the
    pointwise-evaluated substitutions.  The algebraic core of the `compose`↔pointwise bridge. -/
theorem aeval_eval_point {ι : Type*} (σ : ι → F[X]) (x : F) (M : MvPolynomial ι F) :
    (MvPolynomial.aeval σ M).eval x = MvPolynomial.eval (fun i => (σ i).eval x) M := by
  induction M using MvPolynomial.induction_on with
  | C a => simp [Polynomial.algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

/-- The generic `RAP.compose` (the paper's `Y_{i,j} ↦ P_i(ω^j·X)`), evaluated at a
    trace-domain point `x`, is the multivariate evaluation of `C_i` at `P_i(ω^j·x)`. -/
theorem compose_eval (R : RAP F) (P : Fin R.w → F[X]) (i : Fin R.s) (x : F) :
    (R.compose P i).eval x
      = MvPolynomial.eval (fun q : Fin R.w × ℕ => (P q.1).eval (R.ω ^ (q.2 : ℕ) * x)) (R.C i) := by
  rw [RAP.compose, aeval_eval_point]
  refine congrArg (fun f => MvPolynomial.eval f (R.C i)) ?_
  funext q
  simp [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

/-- The per-constraint reified polynomials of a `Reified.AIR`. -/
noncomputable def airC (air : Reified.AIR) (chalVal pubVal : ℕ → F) :
    Fin air.constraints.length → MvPolynomial (Fin air.numTraceCols × ℕ) F :=
  fun i => exprToMv chalVal pubVal (air.constraints.get i).expr

/-- **Assemble a `Reified.AIR` into a generic `Framework.RAP`.**  The trace width
    is `air.numTraceCols`; the constraint set is the reified `airC`; the symbolic-variable index set
    is the paper's adjacent-row `I = [w] × {0,1}`; `d` is the maximal constraint
    degree.  The domain data `(e,h,ω,β,H)` — the "common RAP parameters" of `Def:Canonical_RAP`
 that the deep AIR does not itself carry — are supplied as parameters. -/
@[reducible] noncomputable def airToRAP (air : Reified.AIR) (chalVal pubVal : ℕ → F)
    (eDeg hExp : ℕ) (ω β : F) (H : Finset F) (hβ : β ≠ 0) (hh1 : 1 ≤ hExp) : RAP F where
  e := eDeg
  k := 1
  wRAP := fun _ => air.numTraceCols
  w := air.numTraceCols
  w_eq := by simp
  h := hExp
  d := Finset.univ.sup (fun i => (airC air chalVal pubVal i).totalDegree)
  s := air.constraints.length
  ω := ω
  β := β
  I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
  C := airC air chalVal pubVal
  C_vars := fun i => exprToMv_vars chalVal pubVal (air.constraints.get i).expr
  C_deg := fun i =>
    Finset.le_sup (f := fun i => (airC air chalVal pubVal i).totalDegree) (Finset.mem_univ i)
  H := H
  β_ne_zero := hβ
  I_bound := by
    intro q hq
    have hq2 : q.2 = 0 ∨ q.2 = 1 := by
      have h2 := (Finset.mem_product.mp hq).2
      simpa [Finset.mem_insert, Finset.mem_singleton] using h2
    have hge : 2 ≤ 2 ^ hExp := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ hExp := Nat.pow_le_pow_right (by norm_num) hh1
    rcases hq2 with h | h <;> rw [h] <;> omega

/-- **KEY CORRESPONDENCE (`Def RAP` satisfaction).**  A trace `P` of univariate
    polynomials satisfies the reified RAP `airToRAP air …` **iff** every deep-embedded constraint of
    `air` evaluates to `0` at every trace-domain point `x ∈ H`, reading each column `i` at `x`
    (current row) and `ω·x` (next row) — exactly the paper's assignment `Y_{i,j} ↦ P_i(ω^j·X)`.
    This is the exact bridge between the concrete reified AIR (`Nock.AIR`) and the generic `RAP`. -/
theorem airToRAP_satisfies_iff (air : Reified.AIR) (chalVal pubVal : ℕ → F)
    (eDeg hExp : ℕ) (ω β : F) (H : Finset F) (hβ : β ≠ 0) (hh1 : 1 ≤ hExp)
    (P : Fin air.numTraceCols → F[X]) :
    (airToRAP air chalVal pubVal eDeg hExp ω β H hβ hh1).Satisfies P
      ↔ ∀ x ∈ H, ∀ c ∈ air.constraints,
          c.expr.eval (envOfTrace P ω x chalVal pubVal) = 0 := by
  have key : ∀ (i : Fin air.constraints.length) (x : F),
      ((airToRAP air chalVal pubVal eDeg hExp ω β H hβ hh1).compose P i).eval x
        = (air.constraints.get i).expr.eval (envOfTrace P ω x chalVal pubVal) := by
    intro i x
    rw [compose_eval]
    simp only [airToRAP, airC]
    rw [eval_exprToMv]
  constructor
  · intro hsat x hx c hc
    obtain ⟨i, hget⟩ := List.mem_iff_get.mp hc
    have hz := hsat i x hx
    rw [key i x] at hz
    rw [← hget]
    exact hz
  · intro hall i x hx
    rw [key i x]
    exact hall x hx (air.constraints.get i) (List.get_mem _ _)

end Reify

/-! ## INSTANCE: Nock as a `MES` / `CanonicalRAP` instance

  Both instances instantiate the framework interface with the **genuine** Nock objects: the compute
  verifier is `RVT Fcomp` membership and the memory verifier `RVT Fmem` membership (the traversable
  RVT languages, `nock_traversable`), linked by the shared IO in `L_mIO` (`Nock.IO.LmIO`). The
  single separation/RAP equivalence that these interfaces require — `x ∈ LangVM ⟺ (RVT-decomposition
  + IO-linking)`, resp. `LangVMComputation ⟺ RAP-satisfiability` —
  is the content of the §5 capstone `V_NockVMROM` and the table equivalences
  `equiv_compute`/`equiv_mem`, proved in `Nock.NockVM`/`Nock.ComputeTable`/
  `Nock.MemoryTable`. **FLAGGED (see report).**

  Two concrete
  obstacles, both genuine (not a wiring omission):
  1. **Shape.**  `MES.correct` (Def:MES) is a *deterministic, exact* biconditional
     about verifier acceptance: `(∃T, LangVM x T) ↔ (∃ decomposition …)`.  `V_NockVMROM_forest`
 proves the *probabilistic soundness* capstone: a conjunction of two
     bad-challenge cardinality bounds `walkBad/walkBadForest ≤ h/|K| + ε_RLC` **plus** an IO
     biconditional `(∃ accumulators …) ↔ IO.LIO …` (conjunct 3).  Its only per-verifier content is
     the *one-directional* `equiv_compute_sound`/`equiv_mem_sound` (RAP-sat ⇒ `Fcomp`/`Fmem`),
     wrapped in a probability bound — strictly different from, and neither implies, the deterministic
     `↔` that `MES.correct` requires.
  2. **No concrete `LangVM`.**  `nock_MES` is parametric over an *abstract* `LangVM : X → Tw → Prop`;
     the §5 capstone never defines a top-level NockVM language predicate (it takes per-row `RAPcomp`/
     `RAPmem` satisfiability, queue gates, and derived record lists as hypotheses).  Discharging
     `hcorrect` requires first *defining* that concrete `LangVM` and its `splitX`/`splitT` bijections
     (a `Nock.NockVM`-owned task) and then assembling `equiv_compute`/`equiv_mem` (both stated as
     `↔`) with `IO.io_result_LIO` into the exact `MES.correct` shape.
  ⇒ `hcorrect` stays a carried hypothesis; ESCALATED (see report).  The `CanonicalRAP` side, by
  contrast, IS advanced this sprint: `nock_canonicalRAP_ofReified` discharges the two
  `RAP.Satisfies` iffs via the reification correspondence `Reify.airToRAP_satisfies_iff`. -/

/-- **INSTANCE (`Def:MES`).**  The NockVM language `LangVM` is uniquely
    memory-execution separable over any record encoding `M`, with the compute/memory verifiers the
    two traversable RVT languages (`RVT Fcomp` / `RVT Fmem`) and the shared IO in `L_mIO`.  The
    separation equivalence `hcorrect` is the capstone `V_NockVMROM` content (carried; see header). -/
noncomputable def nock_MES (K : Type*) [Field K] (M : MEF) [DecidableEq M.Rec]
    (X Tw : Type*) (Ksz : ℕ) (LangVM : X → Tw → Prop)
    (splitX : X ≃ NTree (State × DTcomp K) × NTree (MState × DTmem K))
    (hcorrect : ∀ x : X, (∃ T, LangVM x T) ↔
      ∃ (_T : Tw) (ioP ioM : List M.Rec),
        RVT (Fcomp (K := K)) (splitX x).1 ∧ RVT (Fmem (K := K)) (splitX x).2
        ∧ Nock.IO.LmIO Ksz ioP ioM) :
    MES X Tw M where
  Xprog := NTree (State × DTcomp K)
  Xmem := NTree (MState × DTmem K)
  Tprog := Tw
  Tmem := PUnit
  IOprog := List M.Rec
  IOmem := List M.Rec
  LangVM := LangVM
  LangVMComputation := fun xp _ _ => RVT (Fcomp (K := K)) xp
  LangVMMemory := fun xm _ _ => RVT (Fmem (K := K)) xm
  splitX := splitX
  splitT := (Equiv.prodPUnit Tw).symm
  K := Ksz
  ioRecords := fun ioP ioM => (ioP, ioM)
  correct := hcorrect

/-- **INSTANCE (`Def:Canonical_RAP`).**  The Nock `MES` instance has a canonical RAP
    arithmetization: two sub-RAPs `Rprog`, `Rmem` sharing the common parameters, with the compute/
    memory verifiers equivalent to RAP-satisfiability.  The satisfaction equivalences (`hprog`,
    `hmem`) are the content of `equiv_compute`/`equiv_mem` composed with the AIR→generic-`RAP`
    reification; that reification is not yet mechanized, so the equivalences are carried (see
    header).  All common-parameter sharing is discharged from the supplied equalities. -/
noncomputable def nock_canonicalRAP {K : Type*} [Field K] {M : MEF} [DecidableEq M.Rec]
    {X Tw : Type*} {Ksz : ℕ} {LangVM : X → Tw → Prop}
    {splitX : X ≃ NTree (State × DTcomp K) × NTree (MState × DTmem K)}
    {hcorrect : ∀ x : X, (∃ T, LangVM x T) ↔
      ∃ (_T : Tw) (ioP ioM : List M.Rec),
        RVT (Fcomp (K := K)) (splitX x).1 ∧ RVT (Fmem (K := K)) (splitX x).2
        ∧ Nock.IO.LmIO Ksz ioP ioM}
    (F : Type*) [CommRing F]
    (Rprog Rmem : RAP F)
    (he : Rprog.e = Rmem.e) (hh : Rprog.h = Rmem.h) (hd : Rprog.d = Rmem.d)
    (hω : Rprog.ω = Rmem.ω) (hβ : Rprog.β = Rmem.β)
    (encP : NTree (State × DTcomp K) → Tw → List M.Rec → (Fin Rprog.w → F[X]))
    (encM : NTree (MState × DTmem K) → PUnit → List M.Rec → (Fin Rmem.w → F[X]))
    (hprog : ∀ xp tp iop, RVT (Fcomp (K := K)) xp ↔ Rprog.Satisfies (encP xp tp iop))
    (hmem : ∀ xm tm iom, RVT (Fmem (K := K)) xm ↔ Rmem.Satisfies (encM xm tm iom)) :
    CanonicalRAP (nock_MES K M X Tw Ksz LangVM splitX hcorrect) F where
  Rprog := Rprog
  Rmem := Rmem
  common_e := he
  common_h := hh
  common_d := hd
  common_ω := hω
  common_β := hβ
  encodeProg := encP
  encodeMem := encM
  compute_iff := hprog
  memory_iff := hmem

/-- Those residual conditions
    are exactly the content of `equiv_compute`/`equiv_mem`,
    stated over the honest trace-encodings `encP`/`encM` and the trace-domain `HP`/`HM` — i.e. the
    carried gap is moved off the un-mechanized `MvPolynomial` reification boundary onto the
    already-mechanized reified-AIR boundary. (Fully closing `hprogR`/`hmemR` — i.e. proving
    `RVT ⟺ all-rows reified-AIR vanishing` over the concrete trace polynomials — is the
    `ComputeTable`/`MemoryTable`-owned remaining step; see report.) -/
noncomputable def nock_canonicalRAP_ofReified {K : Type*} [Field K] {M : MEF} [DecidableEq M.Rec]
    {X Tw : Type*} {Ksz : ℕ} {LangVM : X → Tw → Prop}
    {splitX : X ≃ NTree (State × DTcomp K) × NTree (MState × DTmem K)}
    {hcorrect : ∀ x : X, (∃ T, LangVM x T) ↔
      ∃ (_T : Tw) (ioP ioM : List M.Rec),
        RVT (Fcomp (K := K)) (splitX x).1 ∧ RVT (Fmem (K := K)) (splitX x).2
        ∧ Nock.IO.LmIO Ksz ioP ioM}
    (F : Type*) [Field F]
    -- compute chip: the reified AIR + its RAP domain data
    (airP : Reified.AIR) (chalP pubP : ℕ → F) (eP hP : ℕ) (ωP βP : F) (HP : Finset F)
    (encP : NTree (State × DTcomp K) → Tw → List M.Rec → (Fin airP.numTraceCols → F[X]))
    -- memory chip: the reified AIR + its RAP domain data
    (airM : Reified.AIR) (chalM pubM : ℕ → F) (eM hM : ℕ) (ωM βM : F) (HM : Finset F)
    (encM : NTree (MState × DTmem K) → PUnit → List M.Rec → (Fin airM.numTraceCols → F[X]))
    -- common-parameter sharing (as in `nock_canonicalRAP`)
    (he : eP = eM) (hh : hP = hM)
    (hβP : βP ≠ 0) (hβM : βM ≠ 0) (hhP1 : 1 ≤ hP) (hhM1 : 1 ≤ hM)
    (hd : (Reify.airToRAP airP chalP pubP eP hP ωP βP HP hβP hhP1).d
        = (Reify.airToRAP airM chalM pubM eM hM ωM βM HM hβM hhM1).d)
    (hω : ωP = ωM) (hβ : βP = βM)
    -- the concrete reified-AIR satisfaction iffs (the `equiv_compute`/`equiv_mem` content)
    (hprogR : ∀ (xp : NTree (State × DTcomp K)) (tp : Tw) (iop : List M.Rec),
        RVT (Fcomp (K := K)) xp ↔
          ∀ x ∈ HP, ∀ c ∈ airP.constraints,
            c.expr.eval (Reify.envOfTrace (encP xp tp iop) ωP x chalP pubP) = 0)
    (hmemR : ∀ (xm : NTree (MState × DTmem K)) (tm : PUnit) (iom : List M.Rec),
        RVT (Fmem (K := K)) xm ↔
          ∀ x ∈ HM, ∀ c ∈ airM.constraints,
            c.expr.eval (Reify.envOfTrace (encM xm tm iom) ωM x chalM pubM) = 0) :
    CanonicalRAP (nock_MES K M X Tw Ksz LangVM splitX hcorrect) F where
  Rprog := Reify.airToRAP airP chalP pubP eP hP ωP βP HP hβP hhP1
  Rmem := Reify.airToRAP airM chalM pubM eM hM ωM βM HM hβM hhM1
  common_e := he
  common_h := hh
  common_d := hd
  common_ω := hω
  common_β := hβ
  encodeProg := encP
  encodeMem := encM
  compute_iff := fun xp tp iop =>
    (hprogR xp tp iop).trans
      (Reify.airToRAP_satisfies_iff airP chalP pubP eP hP ωP βP HP hβP hhP1 (encP xp tp iop)).symm
  memory_iff := fun xm tm iom =>
    (hmemR xm tm iom).trans
      (Reify.airToRAP_satisfies_iff airM chalM pubM eM hM ωM βM HM hβM hhM1 (encM xm tm iom)).symm

end Nock.Framework
