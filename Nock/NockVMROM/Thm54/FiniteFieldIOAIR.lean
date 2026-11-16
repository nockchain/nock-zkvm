import Nock.AIR
import Nock.NockVMROM.Thm54.FiniteFieldIO

/-!
# The prover-committed finite-field IO AIR

The symbolic IO AIRs (`Nock.Reified.Trans.ioProgAIR` / `ioMemAIR`) live over `RatFunc L` and have
`0` challenge columns: their per-row fraction column is verifier reconstructed as `SetEq.frac`,
so there is no inverse gate.  This module reifies the finite-`K` replacement described in the
header of the IO block of `Nock/AIR.lean`:

* two challenge columns — `chal 0 = gamma` (record RLC) and `chal 1 = pole` (LogUp pole);
* an explicit record-RLC gate over the `m` committed record columns;
* a genuine **inverse gate** `(pole + RLC^gamma(record)) · inv = 1` pinning the committed
  reciprocal column;
* explicit `K`-valued multiplicity and multiplicity-inverse columns on the response side;
* accumulator init / transition / terminal gates.

Every constraint is an `Expr` evaluated in `Env K` for the plain field `K`: no `RatFunc`
anywhere.  The per-record gates are `.transition`-gated (Plonky3 `when_transition`), so they are
imposed exactly on the `records` record rows and not on the extra terminal accumulator row.

`reified_finiteIOProg_sound` / `reified_finiteIOMem_sound` / `reified_finiteIO_sound` are tight
biconditionals against `FiniteIO.FiniteIOAccepts`, in the style of the existing
`Nock.Reified.Trans.reified_io_prog_sound`.
-/

namespace Nock.NockVMROM.Thm54.FiniteIO

open Nock Nock.Reified
open scoped BigOperators

/-! ## The record-RLC expression -/

/-- `RLC^gamma` over the `m` committed record columns based at `base`, as reified data:
    `Σ_{c<m} chal(0)^c · trace(base + c)`. -/
def rlcExpr : ℕ → ℕ → Expr
  | 0, _ => .Const 0
  | (m + 1), base => .Add (rlcExpr m base) (.Mul (.Pow (chl 0) m) (tc (base + m)))

/-- Evaluation of the reified record-RLC expression. -/
theorem rlcExpr_eval {K : Type*} [Field K] (m base : ℕ) (env : Env K) :
    (rlcExpr m base).eval env = ∑ c ∈ Finset.range m, env.chal 0 ^ c * env.trace (base + c) := by
  induction m with
  | zero => simp [rlcExpr, Expr.eval]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

/-! ## Row environments -/

variable {K : Type*} [Field K] {m : ℕ}

/-- **The finite-field IO row environment.**  Column `0` is the accumulator, column `1` the
    committed reciprocal, columns `2` and `3` the multiplicity and its inverse (unused on the
    request side), and columns `recBase … recBase + m − 1` the committed record.  The two
    challenge slots carry the sampled coins; public slot `0` is the shared terminal. -/
def ioRowEnv (coins : IOCoins K) (recBase : ℕ) (acc inv mult multInv terminal : K)
    (rec : Fin m → K) : Env K where
  trace := fun j =>
    if j = 0 then acc
    else if j = 1 then inv
    else if j = 2 then mult
    else if j = 3 then multInv
    else if h : j - recBase < m ∧ recBase ≤ j then rec ⟨j - recBase, h.1⟩ else 0
  traceNext := fun _ => 0
  chal := fun j => if j = 0 then coins.gamma else if j = 1 then coins.pole else 0
  pub := fun j => if j = 0 then terminal else 0

/-- The record columns of the row environment read back the committed record (`recBase ≥ 4`). -/
theorem ioRowEnv_rec {coins : IOCoins K} {recBase : ℕ} (hbase : 4 ≤ recBase)
    {acc inv mult multInv terminal : K} {rec : Fin m → K} (c : Fin m) :
    (ioRowEnv coins recBase acc inv mult multInv terminal rec).trace (recBase + (c : ℕ))
      = rec c := by
  have h0 : recBase + (c : ℕ) ≠ 0 := by omega
  have h1 : recBase + (c : ℕ) ≠ 1 := by omega
  have h2 : recBase + (c : ℕ) ≠ 2 := by omega
  have h3 : recBase + (c : ℕ) ≠ 3 := by omega
  have h4 : recBase + (c : ℕ) - recBase < m ∧ recBase ≤ recBase + (c : ℕ) := by
    refine ⟨?_, by omega⟩
    have := c.isLt; omega
  show (if _ then _ else _) = _
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, dif_pos h4]
  refine congrArg rec (Fin.ext ?_)
  show recBase + (c : ℕ) - recBase = (c : ℕ)
  omega

/-- The reified record-RLC gate computes `Walk.rlc` of the committed record. -/
theorem rlcExpr_eval_rowEnv {coins : IOCoins K} {recBase : ℕ} (hbase : 4 ≤ recBase)
    {acc inv mult multInv terminal : K} {rec : Fin m → K} :
    (rlcExpr m recBase).eval
        (ioRowEnv coins recBase acc inv mult multInv terminal rec)
      = Walk.rlc coins.gamma rec := by
  rw [rlcExpr_eval, Finset.sum_range]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [ioRowEnv_rec hbase c]
  rfl

@[simp] theorem ioRowEnv_acc (coins : IOCoins K) (recBase : ℕ)
    (acc inv mult multInv terminal : K) (rec : Fin m → K) :
    (ioRowEnv coins recBase acc inv mult multInv terminal rec).trace 0 = acc := rfl

@[simp] theorem ioRowEnv_inv (coins : IOCoins K) (recBase : ℕ)
    (acc inv mult multInv terminal : K) (rec : Fin m → K) :
    (ioRowEnv coins recBase acc inv mult multInv terminal rec).trace 1 = inv := rfl

@[simp] theorem ioRowEnv_mult (coins : IOCoins K) (recBase : ℕ)
    (acc inv mult multInv terminal : K) (rec : Fin m → K) :
    (ioRowEnv coins recBase acc inv mult multInv terminal rec).trace 2 = mult := rfl

@[simp] theorem ioRowEnv_multInv (coins : IOCoins K) (recBase : ℕ)
    (acc inv mult multInv terminal : K) (rec : Fin m → K) :
    (ioRowEnv coins recBase acc inv mult multInv terminal rec).trace 3 = multInv := rfl

@[simp] theorem ioRowEnv_pole (coins : IOCoins K) (recBase : ℕ)
    (acc inv mult multInv terminal : K) (rec : Fin m → K) :
    (ioRowEnv coins recBase acc inv mult multInv terminal rec).chal 1 = coins.pole := rfl

@[simp] theorem ioRowEnv_terminal (coins : IOCoins K) (recBase : ℕ)
    (acc inv mult multInv terminal : K) (rec : Fin m → K) :
    (ioRowEnv coins recBase acc inv mult multInv terminal rec).pub 0 = terminal := rfl

/-! ## The gates -/

/-- **The inverse gate** (the constraint the symbolic `RatFunc` AIR does not have):
    `(pole + RLC^gamma(record)) · inv − 1 = 0`. -/
def ioInvPin (m recBase : ℕ) : Expr :=
  .Sub (.Mul (.Add (chl 1) (rlcExpr m recBase)) (tc 1)) (.Const 1)

/-- Accumulator initial gate: `acc = 0`. -/
def ioAccInit : Expr := tc 0

/-- Request-side accumulation: `acc' − acc − inv = 0`. -/
def ioProgAccStep : Expr := .Sub (.Sub (Trans.tn 0) (tc 0)) (tc 1)

/-- Response-side accumulation: `acc' − acc − mult · inv = 0`. -/
def ioMemAccStep : Expr := .Sub (.Sub (Trans.tn 0) (tc 0)) (.Mul (tc 2) (tc 1))

/-- Multiplicity booleanity. -/
def ioMultBool : Expr := .Mul (tc 2) (.Sub (tc 2) (.Const 1))

/-- Multiplicity inverse pin (the paper's `m_j ≠ 0`). -/
def ioMultInvPin : Expr := .Sub (.Mul (tc 2) (tc 3)) (.Const 1)

/-- Terminal endpoint gate: `terminal − acc = 0`. -/
def ioTerm : Expr := .Sub (Trans.pubv 0) (tc 0)

/-! ## The exported AIRs -/

/-- **Prover-committed finite-field request-IO AIR.**  `m + 4` trace columns (acc, inv, the two
    unused multiplicity slots kept for a uniform row layout, then the `m` record columns), the
    two sampled challenges, and one public terminal. -/
def finiteIOProgAIR (m : ℕ) : AIR where
  numTraceCols := m + 4
  numChallenges := 2
  numPublic := 1
  constraints :=
    [ ⟨.boundary, ioAccInit⟩, ⟨.transition, ioInvPin m 4⟩,
      ⟨.transition, ioProgAccStep⟩, ⟨.terminal, ioTerm⟩ ]

/-- **Prover-committed finite-field response-IO AIR.**  Same layout, plus the multiplicity
    booleanity and multiplicity-inverse gates. -/
def finiteIOMemAIR (m : ℕ) : AIR where
  numTraceCols := m + 4
  numChallenges := 2
  numPublic := 1
  constraints :=
    [ ⟨.boundary, ioAccInit⟩, ⟨.transition, ioInvPin m 4⟩,
      ⟨.transition, ioMultBool⟩, ⟨.transition, ioMultInvPin⟩,
      ⟨.transition, ioMemAccStep⟩, ⟨.terminal, ioTerm⟩ ]

@[simp] theorem finiteIOProgAIR_numChallenges (m : ℕ) :
    (finiteIOProgAIR m).numChallenges = 2 := rfl
@[simp] theorem finiteIOProgAIR_numTraceCols (m : ℕ) :
    (finiteIOProgAIR m).numTraceCols = m + 4 := rfl
@[simp] theorem finiteIOProgAIR_num_constraints (m : ℕ) :
    (finiteIOProgAIR m).constraints.length = 4 := rfl
@[simp] theorem finiteIOMemAIR_numChallenges (m : ℕ) :
    (finiteIOMemAIR m).numChallenges = 2 := rfl
@[simp] theorem finiteIOMemAIR_numTraceCols (m : ℕ) :
    (finiteIOMemAIR m).numTraceCols = m + 4 := rfl
@[simp] theorem finiteIOMemAIR_num_constraints (m : ℕ) :
    (finiteIOMemAIR m).constraints.length = 6 := rfl

/-! ## Scalar gate soundness -/

section Scalar

variable (coins : IOCoins K) (acc accNext inv mult multInv terminal : K) (rec : Fin m → K)

/-- The inverse gate evaluates to zero iff the committed reciprocal inverts the compressed
    denominator. -/
theorem ioInvPin_sound :
    (ioInvPin m 4).eval (ioRowEnv coins 4 acc inv mult multInv terminal rec) = 0
      ↔ compress coins rec * inv = 1 := by
  simp only [ioInvPin, Expr.eval, chl, tc, ioRowEnv_pole, ioRowEnv_inv, Int.cast_one]
  rw [rlcExpr_eval_rowEnv (le_refl 4), sub_eq_zero]
  exact Iff.rfl

/-- The accumulator initial gate evaluates to zero iff the accumulator starts empty. -/
theorem ioAccInit_sound :
    ioAccInit.eval (ioRowEnv coins 4 acc inv mult multInv terminal rec) = 0 ↔ acc = 0 :=
  Iff.rfl

/-- Request-side accumulation gate. -/
theorem ioProgAccStep_sound (rec' : Fin m → K) (inv' mult' multInv' : K) :
    ioProgAccStep.eval
        (Trans.twoRow (ioRowEnv coins 4 acc inv mult multInv terminal rec)
          (ioRowEnv coins 4 accNext inv' mult' multInv' terminal rec')) = 0
      ↔ accNext = acc + inv := by
  show accNext - acc - inv = 0 ↔ _
  rw [sub_sub, sub_eq_zero]

/-- Response-side accumulation gate. -/
theorem ioMemAccStep_sound (rec' : Fin m → K) (inv' mult' multInv' : K) :
    ioMemAccStep.eval
        (Trans.twoRow (ioRowEnv coins 4 acc inv mult multInv terminal rec)
          (ioRowEnv coins 4 accNext inv' mult' multInv' terminal rec')) = 0
      ↔ accNext = acc + mult * inv := by
  show accNext - acc - mult * inv = 0 ↔ _
  rw [sub_sub, sub_eq_zero]

/-- Multiplicity booleanity gate. -/
theorem ioMultBool_sound :
    ioMultBool.eval (ioRowEnv coins 4 acc inv mult multInv terminal rec) = 0
      ↔ mult * (mult - 1) = 0 := by
  simp only [ioMultBool, Expr.eval, tc, ioRowEnv_mult, Int.cast_one]

/-- Multiplicity inverse gate. -/
theorem ioMultInvPin_sound :
    ioMultInvPin.eval (ioRowEnv coins 4 acc inv mult multInv terminal rec) = 0
      ↔ mult * multInv = 1 := by
  simp only [ioMultInvPin, Expr.eval, tc, ioRowEnv_mult, ioRowEnv_multInv, Int.cast_one]
  rw [sub_eq_zero]

/-- Terminal endpoint gate. -/
theorem ioTerm_sound :
    ioTerm.eval (ioRowEnv coins 4 acc inv mult multInv terminal rec) = 0 ↔ acc = terminal := by
  show terminal - acc = 0 ↔ _
  rw [sub_eq_zero, eq_comm]

end Scalar

/-! ## Row-indexed instantiation -/

variable (records : PreChallengeRecords K m) (coins : IOCoins K)

/-- Request-side row environment at row `i` (rows `0 … requests.length`; the record columns of
    the final accumulator row are zero, and no per-record gate is imposed there). -/
noncomputable def progEnvAt (w : PostChallengeIOWitness records coins) (i : ℕ) : Env K :=
  ioRowEnv coins 4
    (if h : i < records.requests.length + 1 then w.requestAcc ⟨i, h⟩ else 0)
    (if h : i < records.requests.length then w.requestInv ⟨i, h⟩ else 0)
    1 1 w.terminal
    (if h : i < records.requests.length then records.requests.get ⟨i, h⟩ else 0)

/-- Response-side row environment at row `j`. -/
noncomputable def memEnvAt (w : PostChallengeIOWitness records coins) (j : ℕ) : Env K :=
  ioRowEnv coins 4
    (if h : j < records.responses.length + 1 then w.responseAcc ⟨j, h⟩ else 0)
    (if h : j < records.responses.length then w.responseInv ⟨j, h⟩ else 0)
    (if h : j < records.responses.length then w.multiplicity ⟨j, h⟩ else 0)
    (if h : j < records.responses.length then w.multInv ⟨j, h⟩ else 0)
    w.terminal
    (if h : j < records.responses.length then records.responses.get ⟨j, h⟩ else 0)

variable (w : PostChallengeIOWitness records coins)

/-- **`reified_finiteIOProg_sound` (tight biconditional).**  The four request-side gates of
    `finiteIOProgAIR` evaluate to zero at every row exactly when the request-side conjuncts of
    `FiniteIOAccepts` hold. -/
theorem reified_finiteIOProg_sound :
    (ioAccInit.eval (progEnvAt records coins w 0) = 0
      ∧ (∀ i, i < records.requests.length →
          (ioInvPin m 4).eval (progEnvAt records coins w i) = 0)
      ∧ (∀ i, i < records.requests.length →
          ioProgAccStep.eval (Trans.twoRow (progEnvAt records coins w i)
            (progEnvAt records coins w (i + 1))) = 0)
      ∧ ioTerm.eval (progEnvAt records coins w records.requests.length) = 0)
    ↔ (w.requestAcc 0 = 0
        ∧ (∀ i, compress coins (records.requests.get i) * w.requestInv i = 1)
        ∧ (∀ i : Fin records.requests.length,
            w.requestAcc i.succ = w.requestAcc i.castSucc + w.requestInv i)
        ∧ w.requestAcc (Fin.last _) = w.terminal) := by
  classical
  set k := records.requests.length with hk
  have hinit : (ioAccInit.eval (progEnvAt records coins w 0) = 0) ↔ w.requestAcc 0 = 0 := by
    rw [progEnvAt, ioAccInit_sound, dif_pos (Nat.succ_pos k)]
    rfl
  have hterm : (ioTerm.eval (progEnvAt records coins w k) = 0)
      ↔ w.requestAcc (Fin.last k) = w.terminal := by
    rw [progEnvAt, ioTerm_sound, dif_pos (Nat.lt_succ_self k)]
    rfl
  have hpin : (∀ i, i < k → (ioInvPin m 4).eval (progEnvAt records coins w i) = 0)
      ↔ (∀ i : Fin k, compress coins (records.requests.get i) * w.requestInv i = 1) := by
    constructor
    · intro h i
      have hi := h (i : ℕ) i.isLt
      rw [progEnvAt, ioInvPin_sound, dif_pos i.isLt, dif_pos i.isLt] at hi
      simpa using hi
    · intro h i hi
      rw [progEnvAt, ioInvPin_sound, dif_pos hi, dif_pos hi]
      exact h ⟨i, hi⟩
  have hstep : (∀ i, i < k →
        ioProgAccStep.eval (Trans.twoRow (progEnvAt records coins w i)
          (progEnvAt records coins w (i + 1))) = 0)
      ↔ (∀ i : Fin k, w.requestAcc i.succ = w.requestAcc i.castSucc + w.requestInv i) := by
    constructor
    · intro h i
      have hi := h (i : ℕ) i.isLt
      rw [progEnvAt, progEnvAt, ioProgAccStep_sound,
        dif_pos (Nat.lt_succ_of_lt i.isLt), dif_pos (Nat.succ_lt_succ i.isLt),
        dif_pos i.isLt] at hi
      exact hi
    · intro h i hi
      rw [progEnvAt, progEnvAt, ioProgAccStep_sound,
        dif_pos (Nat.lt_succ_of_lt hi), dif_pos (Nat.succ_lt_succ hi), dif_pos hi]
      exact h ⟨i, hi⟩
  rw [hinit, hpin, hstep, hterm]

/-- **`reified_finiteIOMem_sound` (tight biconditional).**  The six response-side gates of
    `finiteIOMemAIR` evaluate to zero at every row exactly when the response-side conjuncts of
    `FiniteIOAccepts` hold. -/
theorem reified_finiteIOMem_sound :
    (ioAccInit.eval (memEnvAt records coins w 0) = 0
      ∧ (∀ j, j < records.responses.length →
          (ioInvPin m 4).eval (memEnvAt records coins w j) = 0)
      ∧ (∀ j, j < records.responses.length →
          ioMultBool.eval (memEnvAt records coins w j) = 0)
      ∧ (∀ j, j < records.responses.length →
          ioMultInvPin.eval (memEnvAt records coins w j) = 0)
      ∧ (∀ j, j < records.responses.length →
          ioMemAccStep.eval (Trans.twoRow (memEnvAt records coins w j)
            (memEnvAt records coins w (j + 1))) = 0)
      ∧ ioTerm.eval (memEnvAt records coins w records.responses.length) = 0)
    ↔ (w.responseAcc 0 = 0
        ∧ (∀ j, compress coins (records.responses.get j) * w.responseInv j = 1)
        ∧ (∀ j, w.multiplicity j * (w.multiplicity j - 1) = 0)
        ∧ (∀ j, w.multiplicity j * w.multInv j = 1)
        ∧ (∀ j : Fin records.responses.length,
            w.responseAcc j.succ
              = w.responseAcc j.castSucc + w.multiplicity j * w.responseInv j)
        ∧ w.responseAcc (Fin.last _) = w.terminal) := by
  classical
  set k := records.responses.length with hk
  have hinit : (ioAccInit.eval (memEnvAt records coins w 0) = 0) ↔ w.responseAcc 0 = 0 := by
    rw [memEnvAt, ioAccInit_sound, dif_pos (Nat.succ_pos k)]
    rfl
  have hterm : (ioTerm.eval (memEnvAt records coins w k) = 0)
      ↔ w.responseAcc (Fin.last k) = w.terminal := by
    rw [memEnvAt, ioTerm_sound, dif_pos (Nat.lt_succ_self k)]
    rfl
  have hpin : (∀ j, j < k → (ioInvPin m 4).eval (memEnvAt records coins w j) = 0)
      ↔ (∀ j : Fin k, compress coins (records.responses.get j) * w.responseInv j = 1) := by
    constructor
    · intro h j
      have hj := h (j : ℕ) j.isLt
      rw [memEnvAt, ioInvPin_sound, dif_pos j.isLt, dif_pos j.isLt] at hj
      simpa using hj
    · intro h j hj
      rw [memEnvAt, ioInvPin_sound, dif_pos hj, dif_pos hj]
      exact h ⟨j, hj⟩
  have hbool : (∀ j, j < k → ioMultBool.eval (memEnvAt records coins w j) = 0)
      ↔ (∀ j : Fin k, w.multiplicity j * (w.multiplicity j - 1) = 0) := by
    constructor
    · intro h j
      have hj := h (j : ℕ) j.isLt
      rw [memEnvAt, ioMultBool_sound, dif_pos j.isLt] at hj
      exact hj
    · intro h j hj
      rw [memEnvAt, ioMultBool_sound, dif_pos hj]
      exact h ⟨j, hj⟩
  have hminv : (∀ j, j < k → ioMultInvPin.eval (memEnvAt records coins w j) = 0)
      ↔ (∀ j : Fin k, w.multiplicity j * w.multInv j = 1) := by
    constructor
    · intro h j
      have hj := h (j : ℕ) j.isLt
      rw [memEnvAt, ioMultInvPin_sound, dif_pos j.isLt, dif_pos j.isLt] at hj
      exact hj
    · intro h j hj
      rw [memEnvAt, ioMultInvPin_sound, dif_pos hj, dif_pos hj]
      exact h ⟨j, hj⟩
  have hstep : (∀ j, j < k →
        ioMemAccStep.eval (Trans.twoRow (memEnvAt records coins w j)
          (memEnvAt records coins w (j + 1))) = 0)
      ↔ (∀ j : Fin k, w.responseAcc j.succ
            = w.responseAcc j.castSucc + w.multiplicity j * w.responseInv j) := by
    constructor
    · intro h j
      have hj := h (j : ℕ) j.isLt
      rw [memEnvAt, memEnvAt, ioMemAccStep_sound,
        dif_pos (Nat.lt_succ_of_lt j.isLt), dif_pos (Nat.succ_lt_succ j.isLt),
        dif_pos j.isLt, dif_pos j.isLt] at hj
      exact hj
    · intro h j hj
      rw [memEnvAt, memEnvAt, ioMemAccStep_sound,
        dif_pos (Nat.lt_succ_of_lt hj), dif_pos (Nat.succ_lt_succ hj),
        dif_pos hj, dif_pos hj]
      exact h ⟨j, hj⟩
  rw [hinit, hpin, hbool, hminv, hstep, hterm]

/-- **`reified_finiteIO_sound`.**  The two finite-field IO AIRs' gates, evaluated at the
    prover-committed rows, hold exactly when `FiniteIOAccepts` holds.  This is the finite-`K`
    analogue of `Nock.Reified.Trans.reified_io_prog_sound` / `reified_io_mem_sound`, upgraded
    with the inverse gate the symbolic `RatFunc` AIR could not carry. -/
theorem reified_finiteIO_sound :
    ((ioAccInit.eval (progEnvAt records coins w 0) = 0
        ∧ (∀ i, i < records.requests.length →
            (ioInvPin m 4).eval (progEnvAt records coins w i) = 0)
        ∧ (∀ i, i < records.requests.length →
            ioProgAccStep.eval (Trans.twoRow (progEnvAt records coins w i)
              (progEnvAt records coins w (i + 1))) = 0)
        ∧ ioTerm.eval (progEnvAt records coins w records.requests.length) = 0)
      ∧ (ioAccInit.eval (memEnvAt records coins w 0) = 0
        ∧ (∀ j, j < records.responses.length →
            (ioInvPin m 4).eval (memEnvAt records coins w j) = 0)
        ∧ (∀ j, j < records.responses.length →
            ioMultBool.eval (memEnvAt records coins w j) = 0)
        ∧ (∀ j, j < records.responses.length →
            ioMultInvPin.eval (memEnvAt records coins w j) = 0)
        ∧ (∀ j, j < records.responses.length →
            ioMemAccStep.eval (Trans.twoRow (memEnvAt records coins w j)
              (memEnvAt records coins w (j + 1))) = 0)
        ∧ ioTerm.eval (memEnvAt records coins w records.responses.length) = 0))
    ↔ FiniteIOAccepts records coins w := by
  rw [reified_finiteIOProg_sound, reified_finiteIOMem_sound]
  constructor
  · rintro ⟨⟨hi1, hp1, hs1, ht1⟩, ⟨hi2, hp2, hb2, hm2, hs2, ht2⟩⟩
    exact { requestInvPin := hp1, responseInvPin := hp2, multBool := hb2, multInvPin := hm2,
            requestInit := hi1, requestStep := hs1, responseInit := hi2, responseStep := hs2,
            requestTerm := ht1, responseTerm := ht2 }
  · intro h
    exact ⟨⟨h.requestInit, h.requestInvPin, h.requestStep, h.requestTerm⟩,
           ⟨h.responseInit, h.responseInvPin, h.multBool, h.multInvPin, h.responseStep,
            h.responseTerm⟩⟩

end Nock.NockVMROM.Thm54.FiniteIO
