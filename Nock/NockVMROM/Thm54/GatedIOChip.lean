import Nock.NockVMROM.Thm54.GigaRAPAssembledWitness

/-!
# The selector-gated `K`-valued IO chip

`Nock/NockVMROM/Thm54/FiniteFieldIOAIR.lean`'s request-side chip is **ungated**: its two
per-record gates

* `ioInvPin` (`FiniteFieldIOAIR.lean:127`) — `(pole + RLC^γ(record)) · inv − 1 = 0`, and
* `ioProgAccStep` (`:134`) — `acc' − acc − inv = 0`

carry no selector factor, so *every* transition row of `finiteIOProgAIR` must carry a record with
a nonzero compressed denominator and must move the accumulator.

The paper's specification of the same constraint is selector-gated.  Re-read at source:

* the paper — `io(i) := Σ_{j ∈ OP_IO} x_prog(i,j)`, the IO selector, defined as a **sum of
  the compute table's opcode-selector columns**, not as a free committed column;
* the paper — the aggregation constraint's left-hand side carries the `x_prog(i,l)` opcode
  factor;
* the paper — its right-hand side carries `(acc_prog(i) − acc_prog(i−1)) · (1 − io(i))`,
  which forces the accumulator *unchanged* on a row with no IO;
* the paper — in words: "at each row `i`, **if** the active opcode is an element of `OP_IO`
  and thus requires memory input, then all the non-zero memory records … are added to the
  accumulator";
* the paper — `ver(i) · (ver(i) − 1) = 0`, the response side's booleanity of its own
  selector, and the paper the response side's `ver`-gated accumulation.

**Direction.**  An ungated constraint is *stronger*, so the tree's chip cannot admit a false
proof: soundness of every existing statement is untouched by this module, which adds a new AIR
alongside and edits nothing.

**What this module does not do.**  It does not claim the tree's chip is unsound, and it does not
claim the gated chip is a drop-in replacement: §5 shows explicitly that *nothing inside* the gated
chip pins the selector, so the gated chip alone proves a statement about the **selected** rows.
What pins the selector is external, and it is external in the paper too — the paper makes
`io(i)` a linear form in `x_prog`'s opcode columns, which `RAP_prog`'s own one-hot constraints
pin.  §3 is that reading, stated as a lemma.

The product form of the paper-`:527` (multiply through by the denominators, no explicit
inverse column) versus this tree's committed reciprocal column is a legitimate implementation
difference — LogUp with committed reciprocals — and is not touched here.
-/

namespace Nock.NockVMROM.Thm54.GatedIO

open Nock Nock.Reified Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.IOChip
open scoped BigOperators Polynomial

variable {K : Type*} [Field K] {m : ℕ}

/-! ## 1. The gated gates and the gated AIR

The selector lives in **column `2`**, which the request-side chip leaves free: the constraint list
of `finiteIOProgAIR` is `[ioAccInit, ioInvPin m 4, ioProgAccStep, ioTerm]`, reading columns `0`,
`1` and `4 … m+3` only.  Columns `2` and `3` are, in the words of that AIR's own docstring
(`FiniteFieldIOAIR.lean`, above `:153`), "the two unused multiplicity slots kept for a uniform row
layout".  So the selector costs no extra width. -/

/-- **Selector booleanity** — the paper's `io(i)` is a sum of one-hot opcode selectors, hence
    `0` or `1`; the paper is the response side's own booleanity gate for `ver`. -/
def ioSelBool : Expr := .Mul (tc 2) (.Sub (tc 2) (.Const 1))

/-- **The gated inverse pin** — `sel · ((pole + RLC^γ(record)) · inv − 1) = 0`.  On `sel = 0` the
    committed reciprocal is unconstrained, so a padding row need not carry an invertible
    compressed denominator; on `sel = 1` this is exactly `ioInvPin`. -/
def ioInvPinGated (m recBase : ℕ) : Expr := .Mul (tc 2) (ioInvPin m recBase)

/-- **The gated accumulation step** — `acc' − acc − sel · inv = 0`, the reading of the paper:
    at `sel = 0` the accumulator is unchanged. -/
def ioSelAccStep : Expr := .Sub (.Sub (Trans.tn 0) (tc 0)) (.Mul (tc 2) (tc 1))

/-- **The tree already contains the gated accumulation gate.**  `ioSelAccStep` is *literally*
    `ioMemAccStep` (`FiniteFieldIOAIR.lean:137`): the response side's multiplicity-weighted step
    is the request side's selector-gated step, same expression. -/
theorem ioSelAccStep_eq_ioMemAccStep : (ioSelAccStep : Expr) = ioMemAccStep := rfl

/-- Likewise the selector-booleanity gate is the existing multiplicity-booleanity gate. -/
theorem ioSelBool_eq_ioMultBool : (ioSelBool : Expr) = ioMultBool := rfl

/-- **The selector-gated request-IO AIR.**  Same width, challenge count and public count as
    `finiteIOProgAIR m`; column `2` now carries the selector `io(i)` of the paper. -/
def gatedIOProgAIR (m : ℕ) : AIR where
  numTraceCols := m + 4
  numChallenges := 2
  numPublic := 1
  constraints :=
    [ ⟨.boundary, ioAccInit⟩, ⟨.transition, ioSelBool⟩,
      ⟨.transition, ioInvPinGated m 4⟩, ⟨.transition, ioSelAccStep⟩,
      ⟨.terminal, ioTerm⟩ ]

@[simp] theorem gatedIOProgAIR_numTraceCols (m : ℕ) :
    (gatedIOProgAIR m).numTraceCols = m + 4 := rfl
@[simp] theorem gatedIOProgAIR_numChallenges (m : ℕ) :
    (gatedIOProgAIR m).numChallenges = 2 := rfl
@[simp] theorem gatedIOProgAIR_numPublic (m : ℕ) :
    (gatedIOProgAIR m).numPublic = 1 := rfl
@[simp] theorem gatedIOProgAIR_num_constraints (m : ℕ) :
    (gatedIOProgAIR m).constraints.length = 5 := rfl

/-- The gated chip is exactly as wide as the ungated one: the selector is free. -/
theorem gatedIOProgAIR_width_eq (m : ℕ) :
    (gatedIOProgAIR m).numTraceCols = (finiteIOProgAIR m).numTraceCols := rfl

/-- **The cost of gating is one degree.**  At the deployed record width `m = 8` the gated request
    AIR has maximum constraint degree `3` where the ungated one has `2`: the selector multiplies
    the inverse pin.  (The paper's own product form at the paper, which multiplies through by
    all `regs(l)` denominators instead of committing reciprocals, is higher degree still.) -/
theorem gatedIOProgAIR_maxDegree_eight : (gatedIOProgAIR 8).maxDegree = 3 := by decide

theorem finiteIOProgAIR_maxDegree_eight : (finiteIOProgAIR 8).maxDegree = 2 := by decide

/-! ### Column `2` really was free

The claim that the selector costs no width is not a reading of a docstring: `rlcExpr_eval_congr`
and `finiteIOProgAIR_ignores_selector_slots` prove that **no gate of the ungated request AIR
depends on columns `2` or `3` at all**.  So placing the selector at column `2` neither collides
with an existing gate nor widens the chip. -/

theorem rlcExpr_eval_congr (m base : ℕ) (env env' : Env K)
    (hch : env.chal 0 = env'.chal 0)
    (htr : ∀ c, c < m → env.trace (base + c) = env'.trace (base + c)) :
    (rlcExpr m base).eval env = (rlcExpr m base).eval env' := by
  rw [rlcExpr_eval, rlcExpr_eval, hch]
  exact Finset.sum_congr rfl (fun c hc => by rw [htr c (Finset.mem_range.mp hc)])

/-- **No gate of `finiteIOProgAIR m` reads column `2` or column `3`.**  Two environments that
    agree everywhere except on those two columns give every gate the same value. -/
theorem finiteIOProgAIR_ignores_selector_slots (env env' : Env K)
    (htr : ∀ j, j ≠ 2 → j ≠ 3 → env.trace j = env'.trace j)
    (htn : ∀ j, env.traceNext j = env'.traceNext j)
    (hch : ∀ j, env.chal j = env'.chal j) (hpub : ∀ j, env.pub j = env'.pub j) :
    ∀ c ∈ (finiteIOProgAIR m).constraints, c.expr.eval env = c.expr.eval env' := by
  intro c hc
  have h0 : env.trace 0 = env'.trace 0 := htr 0 (by omega) (by omega)
  have h1 : env.trace 1 = env'.trace 1 := htr 1 (by omega) (by omega)
  have hrlc : (rlcExpr m 4).eval env = (rlcExpr m 4).eval env' :=
    rlcExpr_eval_congr m 4 env env' (hch 0) (fun c _ => htr (4 + c) (by omega) (by omega))
  simp only [finiteIOProgAIR, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simpa only [ioAccInit, Expr.eval, tc] using h0
  · simp only [ioInvPin, Expr.eval, chl, tc]
    rw [hch 1, hrlc, h1]
  · simp only [ioProgAccStep, Expr.eval, Trans.tn, tc]
    rw [htn 0, h0, h1]
  · simp only [ioTerm, Expr.eval, Trans.pubv, tc]
    rw [hpub 0, h0]

/-! ## 2. Scalar gate soundness

`ioRowEnv` (`FiniteFieldIOAIR.lean:58`) is the existing row environment; the selector occupies its
`mult` argument, i.e. column `2`. -/

section Scalar

variable (coins : IOCoins K) (acc accNext inv sel multInv terminal : K) (rec : Fin m → K)

/-- The *equational* form of the ungated inverse pin, which the gated pin multiplies. -/
theorem ioInvPin_eval_ioRowEnv :
    (ioInvPin m 4).eval (ioRowEnv coins 4 acc inv sel multInv terminal rec)
      = compress coins rec * inv - 1 := by
  simp only [ioInvPin, Expr.eval, chl, tc, ioRowEnv_pole, ioRowEnv_inv, Int.cast_one]
  rw [rlcExpr_eval_rowEnv (le_refl 4)]
  rfl

/-- Selector booleanity. -/
theorem ioSelBool_sound :
    ioSelBool.eval (ioRowEnv coins 4 acc inv sel multInv terminal rec) = 0
      ↔ sel * (sel - 1) = 0 := by
  simp only [ioSelBool, Expr.eval, tc, ioRowEnv_mult, Int.cast_one]

/-- **The gated inverse pin.**  Vacuous at `sel = 0`, the ungated pin at `sel = 1`. -/
theorem ioInvPinGated_sound :
    (ioInvPinGated m 4).eval (ioRowEnv coins 4 acc inv sel multInv terminal rec) = 0
      ↔ sel * (compress coins rec * inv - 1) = 0 := by
  show (ioRowEnv coins 4 acc inv sel multInv terminal rec).trace 2
      * (ioInvPin m 4).eval (ioRowEnv coins 4 acc inv sel multInv terminal rec) = 0 ↔ _
  rw [ioRowEnv_mult, ioInvPin_eval_ioRowEnv]

/-- **The gated accumulation step.** -/
theorem ioSelAccStep_sound (rec' : Fin m → K) (inv' sel' multInv' : K) :
    ioSelAccStep.eval
        (Trans.twoRow (ioRowEnv coins 4 acc inv sel multInv terminal rec)
          (ioRowEnv coins 4 accNext inv' sel' multInv' terminal rec')) = 0
      ↔ accNext = acc + sel * inv := by
  show accNext - acc - sel * inv = 0 ↔ _
  rw [sub_sub, sub_eq_zero]

/-- **A padding row is legal.**  At `sel = 0` the gated inverse pin holds *whatever* the record
    and the committed reciprocal are — in particular for the zero record, whose compressed
    denominator may be zero — and the accumulation step forces the accumulator unchanged.  This is
    the paper's `(1 − io(i))` branch. -/
theorem gated_padding_row_legal (h0 : sel = 0) (rec' : Fin m → K) (inv' sel' multInv' : K) :
    ioSelBool.eval (ioRowEnv coins 4 acc inv sel multInv terminal rec) = 0
      ∧ (ioInvPinGated m 4).eval (ioRowEnv coins 4 acc inv sel multInv terminal rec) = 0
      ∧ (ioSelAccStep.eval
          (Trans.twoRow (ioRowEnv coins 4 acc inv sel multInv terminal rec)
            (ioRowEnv coins 4 accNext inv' sel' multInv' terminal rec')) = 0
        ↔ accNext = acc) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ioSelBool_sound, h0, zero_mul]
  · rw [ioInvPinGated_sound, h0, zero_mul]
  · rw [ioSelAccStep_sound, h0, zero_mul, add_zero]

/-- **The ungated chip is recovered at `sel = 1`.** -/
theorem gated_eq_ungated_at_sel_one (h1 : sel = 1) (rec' : Fin m → K)
    (inv' sel' multInv' : K) :
    ((ioInvPinGated m 4).eval (ioRowEnv coins 4 acc inv sel multInv terminal rec) = 0
        ↔ (ioInvPin m 4).eval (ioRowEnv coins 4 acc inv sel multInv terminal rec) = 0)
      ∧ (ioSelAccStep.eval
            (Trans.twoRow (ioRowEnv coins 4 acc inv sel multInv terminal rec)
              (ioRowEnv coins 4 accNext inv' sel' multInv' terminal rec')) = 0
          ↔ ioProgAccStep.eval
            (Trans.twoRow (ioRowEnv coins 4 acc inv sel multInv terminal rec)
              (ioRowEnv coins 4 accNext inv' sel' multInv' terminal rec')) = 0) := by
  constructor
  · rw [ioInvPinGated_sound, ioInvPin_eval_ioRowEnv, h1, one_mul]
  · rw [ioSelAccStep_sound, ioProgAccStep_sound, h1, one_mul]

end Scalar

/-! ## 3. What pins the selector: the paper

`io(i) := Σ_{j ∈ OP_IO} x_prog(i,j)` is **not** a free committed column.  The lemma below is that reading with nothing else in it: a one-hot family summed
over a subset is `1` exactly when the active index lies in the subset, so the selector is boolean
*and* determined by the active opcode.  Nothing about the IO chip's own columns is used. -/

/-- **the paper, as a lemma.**  If `x` is one-hot with active index `a`, then
    `Σ_{j ∈ S} x j` is `1` when `a ∈ S` and `0` otherwise. -/
theorem onehot_sum_eq {ι : Type*} [DecidableEq ι] (x : ι → K) (S : Finset ι) (a : ι)
    (hone : x a = 1) (hzero : ∀ b, b ≠ a → x b = 0) :
    (∑ j ∈ S, x j) = if a ∈ S then 1 else 0 := by
  classical
  by_cases ha : a ∈ S
  · rw [if_pos ha, Finset.sum_eq_single a (fun b _ hb => hzero b hb) (fun h => absurd ha h), hone]
  · rw [if_neg ha]
    refine Finset.sum_eq_zero (fun b hb => hzero b ?_)
    rintro rfl
    exact ha hb

/-- **The selector of the paper is boolean, for free.** -/
theorem onehot_sum_bool {ι : Type*} [DecidableEq ι] (x : ι → K) (S : Finset ι) (a : ι)
    (hone : x a = 1) (hzero : ∀ b, b ≠ a → x b = 0) :
    (∑ j ∈ S, x j) * ((∑ j ∈ S, x j) - 1) = 0 := by
  rw [onehot_sum_eq x S a hone hzero]
  by_cases ha : a ∈ S
  · rw [if_pos ha, sub_self, mul_zero]
  · rw [if_neg ha, zero_mul]

/-- **The selector is `1` exactly on the IO rows.**  This is the external fact a consumer must
    supply to the gated chip; §5 shows the chip cannot supply it itself. -/
theorem onehot_sum_eq_one_iff {ι : Type*} [DecidableEq ι] (x : ι → K) (S : Finset ι) (a : ι)
    (hone : x a = 1) (hzero : ∀ b, b ≠ a → x b = 0) :
    (∑ j ∈ S, x j) = 1 ↔ a ∈ S := by
  rw [onehot_sum_eq x S a hone hzero]
  by_cases ha : a ∈ S
  · simp [ha]
  · simp [ha, (zero_ne_one : (0 : K) ≠ 1)]


/-! ## 4. Row-indexed gated acceptance, and what the accumulator sees

`GatedIOAccepts` is the row-indexed reading of the five gates of `gatedIOProgAIR` on an `N`-row
transition prefix.  It is deliberately **not** indexed by a record *list*: the whole point of a
padded deployment is that the row count `N` and the number of real records are different numbers,
so the records are an `ℕ`-indexed family and the rows beyond the real ones carry whatever the
prover put there. -/

/-- **Gated acceptance on `N` transition rows.**  The five conjuncts are the five gates of
    `gatedIOProgAIR`: the boundary `acc 0 = 0`, selector booleanity, the
    gated inverse pin, the gated accumulation step, and the terminal endpoint. -/
structure GatedIOAccepts (N : ℕ) (coins : IOCoins K) (recs : ℕ → Fin m → K)
    (acc inv sel : ℕ → K) (terminal : K) : Prop where
  /-- The accumulator starts empty. -/
  init : acc 0 = 0
  /-- The selector is boolean. -/
  selBool : ∀ i, i < N → sel i * (sel i - 1) = 0
  invPin : ∀ i, i < N → sel i * (compress coins (recs i) * inv i - 1) = 0
  /-- Accumulation is gated by the selector. -/
  step : ∀ i, i < N → acc (i + 1) = acc i + sel i * inv i
  /-- The terminal endpoint. -/
  term : acc N = terminal

namespace GatedIOAccepts

variable {N : ℕ} {coins : IOCoins K} {recs : ℕ → Fin m → K} {acc inv sel : ℕ → K} {terminal : K}

theorem sel_zero_or_one (h : GatedIOAccepts N coins recs acc inv sel terminal)
    {i : ℕ} (hi : i < N) : sel i = 0 ∨ sel i = 1 := by
  rcases mul_eq_zero.mp (h.selBool i hi) with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- **On a selected row the ungated inverse pin holds.** -/
theorem active_invPin (h : GatedIOAccepts N coins recs acc inv sel terminal)
    {i : ℕ} (hi : i < N) (h1 : sel i = 1) : compress coins (recs i) * inv i = 1 := by
  have := h.invPin i hi
  rw [h1, one_mul, sub_eq_zero] at this
  exact this

/-- **On a selected row the pole misses the record**, exactly as in the ungated chip. -/
theorem active_compress_ne_zero (h : GatedIOAccepts N coins recs acc inv sel terminal)
    {i : ℕ} (hi : i < N) (h1 : sel i = 1) : compress coins (recs i) ≠ 0 :=
  left_ne_zero_of_mul_eq_one (h.active_invPin hi h1)

/-- **On a selected row the committed reciprocal is the reciprocal.** -/
theorem active_inv_eq (h : GatedIOAccepts N coins recs acc inv sel terminal)
    {i : ℕ} (hi : i < N) (h1 : sel i = 1) : inv i = (compress coins (recs i))⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h.active_invPin hi h1)

/-- **A padding row is inert.**  This is the paper's `(1 − io(i))` branch: the accumulator
    does not move, and nothing at all is asserted about the row's record or reciprocal. -/
theorem inert_of_sel_zero (h : GatedIOAccepts N coins recs acc inv sel terminal)
    {i : ℕ} (hi : i < N) (h0 : sel i = 0) : acc (i + 1) = acc i := by
  rw [h.step i hi, h0, zero_mul, add_zero]

/-- The accumulator at row `j` is the partial gated sum. -/
theorem acc_eq_partial_sum (h : GatedIOAccepts N coins recs acc inv sel terminal)
    (j : ℕ) (hj : j ≤ N) : acc j = ∑ i ∈ Finset.range j, sel i * inv i := by
  induction j with
  | zero => simpa using h.init
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih (by omega), h.step k (by omega)]

/-- Row `i`'s contribution is `sel i` times the *actual* reciprocal of its compressed record. -/
theorem contribution (h : GatedIOAccepts N coins recs acc inv sel terminal)
    {i : ℕ} (hi : i < N) : sel i * inv i = sel i * (compress coins (recs i))⁻¹ := by
  rcases h.sel_zero_or_one hi with h0 | h1
  · rw [h0, zero_mul, zero_mul]
  · rw [h1, one_mul, one_mul, h.active_inv_eq hi h1]

/-- **The terminal is the sum over the selected rows.**  Padding rows contribute `0` — this is
    the payoff of the selector, and the reason a padded deployment computes the *same* terminal
    as the unpadded one. -/
theorem terminal_eq_selected_sum (h : GatedIOAccepts N coins recs acc inv sel terminal) :
    terminal = ∑ i ∈ Finset.range N, sel i * (compress coins (recs i))⁻¹ := by
  rw [← h.term, h.acc_eq_partial_sum N (le_refl N)]
  exact Finset.sum_congr rfl (fun i hi => h.contribution (Finset.mem_range.mp hi))

/-- The accumulator is constant across a run of unselected rows. -/
theorem acc_const_of_inactive (h : GatedIOAccepts N coins recs acc inv sel terminal)
    (n : ℕ) (hinact : ∀ i, n ≤ i → i < N → sel i = 0) :
    ∀ j, n ≤ j → j ≤ N → acc j = acc n := by
  intro j hnj hjN
  induction j, hnj using Nat.le_induction with
  | base => rfl
  | succ k hnk ih =>
    rw [h.inert_of_sel_zero (show k < N by omega) (hinact k hnk (by omega)), ih (by omega)]

/-- **Soundness carries over.**  Given the *external* fact that the selected rows are exactly the
    first `n`, the
    gated data on `N` rows is exactly the ungated request-side data on `n` rows — the four
    conjuncts consumed by `IOChip.chip_satisfies` and by `FiniteIO.FiniteIOAccepts`'s request
    half. -/
theorem ungated_of_selected_prefix (h : GatedIOAccepts N coins recs acc inv sel terminal)
    (n : ℕ) (hnN : n ≤ N) (hsel : ∀ i, i < N → (sel i = 1 ↔ i < n)) :
    acc 0 = 0
      ∧ (∀ i, i < n → compress coins (recs i) * inv i = 1)
      ∧ (∀ i, i < n → acc (i + 1) = acc i + inv i)
      ∧ acc n = terminal := by
  have hinact : ∀ i, n ≤ i → i < N → sel i = 0 := by
    intro i hni hiN
    rcases h.sel_zero_or_one hiN with h0 | h1
    · exact h0
    · exact absurd ((hsel i hiN).mp h1) (by omega)
  have hact : ∀ i, i < n → sel i = 1 := fun i hi => (hsel i (by omega)).mpr hi
  refine ⟨h.init, ?_, ?_, ?_⟩
  · intro i hi; exact h.active_invPin (by omega) (hact i hi)
  · intro i hi
    rw [h.step i (by omega), hact i hi, one_mul]
  · rw [← h.term]
    exact (h.acc_const_of_inactive n hinact N hnN (le_refl N)).symm

end GatedIOAccepts

/-! ## 5. What pins the selector — and what happens if nothing does

Read this before treating the gated chip as a replacement for the ungated one.

**Nothing inside the gated chip pins `sel`.**  `gatedIOProgAIR`'s five gates constrain the
selector only to be boolean; a prover free to choose it can set `sel = 0` on a row carrying a real
record and drop that record from the accumulator.  `gated_terminal_not_determined_by_records`
below exhibits exactly that: two accepting column families over the *same* records, with
*different* terminals.

**So the gated chip is strictly weaker than the ungated one, and that is not a defect** — it is
the paper's shape.  In the paper the selector is not a committed column at all: it is
`Σ_{j ∈ OP_IO} x_prog(i,j)`, a linear form in the compute table's opcode selectors, which
`RAP_prog`'s one-hot constraints pin (§3).  A prover who sets `io(i) = 0` on a row whose active
opcode lies in `OP_IO` is not choosing a column, it is falsifying the opcode one-hot.  In this
tree the corresponding fact must arrive as a **cross-chip hypothesis** — the shape of
`GatedIOAccepts.ungated_of_selected_prefix`'s `hsel` — in the same way that
`IOChip.ChipAgreement.record_eq` (`IOChipSoundness.lean:140`) already carries the identification
of the record columns with the record list rather than deriving it.

That trade is the whole content of this module. -/

section NotPinned

local instance factPrime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- **Nothing in the gated chip determines the terminal from the records.**  Over `ZMod 97`, at
    one transition row, the same record (the zero record, whose compressed denominator at
    `(γ, pole) = (0, 1)` is `1`) admits two accepting column families whose terminals are `0` and
    `1`.  So a consumer of the gated chip *must* pin the selector externally; §3 says the paper
    pins it by the opcode one-hot of the paper. -/
theorem gated_terminal_not_determined_by_records :
    ∃ (acc₀ inv₀ sel₀ acc₁ inv₁ sel₁ : ℕ → ZMod 97) (t₀ t₁ : ZMod 97),
      GatedIOAccepts 1 (⟨0, 1⟩ : IOCoins (ZMod 97))
          (fun _ => (0 : Fin 1 → ZMod 97)) acc₀ inv₀ sel₀ t₀
        ∧ GatedIOAccepts 1 (⟨0, 1⟩ : IOCoins (ZMod 97))
          (fun _ => (0 : Fin 1 → ZMod 97)) acc₁ inv₁ sel₁ t₁
        ∧ t₀ ≠ t₁ := by
  have hc : compress (⟨0, 1⟩ : IOCoins (ZMod 97)) (0 : Fin 1 → ZMod 97) = 1 := by
    show (1 : ZMod 97) + Walk.rlc (0 : ZMod 97) (0 : Fin 1 → ZMod 97) = 1
    rw [show Walk.rlc (0 : ZMod 97) (0 : Fin 1 → ZMod 97) = 0 from by simp [Walk.rlc], add_zero]
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0,
          fun i => if i = 0 then 0 else 1, fun _ => 1, fun _ => 1, 0, 1, ?_, ?_, ?_⟩
  · exact { init := rfl
            selBool := fun i _ => by ring
            invPin := fun i _ => by ring
            step := fun i _ => by ring
            term := rfl }
  · refine { init := rfl
             selBool := fun i _ => by ring
             invPin := fun i _ => ?_
             step := fun i hi => ?_
             term := rfl }
    · rw [hc, one_mul, one_mul, sub_self]
    · have hi0 : i = 0 := by omega
      subst hi0
      norm_num
  · decide

end NotPinned


/-! ## 6. Padding legality at the AIR level

The deployment and the interpolation encoder are `IOChipCompleteness`'s own — `chipParams`
(`IOChipCompleteness.lean:161`), `chipTrace` (`:179`), `chipCell` (`:118`) — reused verbatim, with
the selector occupying `chipCell`'s `mult` slot, i.e. column `2`.  The one change is that the
number of transition rows `N` is now **independent of the number of records**. -/

section RowEnv

variable {w : ℕ} (q : SegmentedRAPParams K) (x₀ : K) (P : Fin w → K[X]) (i : ℕ)

theorem ioSelBool_eval_rowEnv :
    ioSelBool.eval (rowEnv q x₀ P i)
      = (rowEnv q x₀ P i).trace 2 * ((rowEnv q x₀ P i).trace 2 - 1) :=
  ioMultBool_eval_rowEnv q x₀ P i

theorem ioSelAccStep_eval_rowEnv :
    ioSelAccStep.eval (rowEnv q x₀ P i)
      = (rowEnv q x₀ P (i + 1)).trace 0 - (rowEnv q x₀ P i).trace 0
          - (rowEnv q x₀ P i).trace 2 * (rowEnv q x₀ P i).trace 1 :=
  ioMemAccStep_eval_rowEnv q x₀ P i

theorem ioInvPinGated_eval_rowEnv (coins : IOCoins K) (rec : Fin m → K)
    (hrec : ∀ c : Fin m, (rowEnv q x₀ P i).trace (4 + (c : ℕ)) = rec c)
    (hγ : q.chalVal 0 = coins.gamma) (hp : q.chalVal 1 = coins.pole) :
    (ioInvPinGated m 4).eval (rowEnv q x₀ P i)
      = (rowEnv q x₀ P i).trace 2
          * (compress coins rec * (rowEnv q x₀ P i).trace 1 - 1) := by
  show (rowEnv q x₀ P i).trace 2 * (ioInvPin m 4).eval (rowEnv q x₀ P i) = _
  rw [ioInvPin_eval_rowEnv q x₀ P i coins rec hrec hγ hp]

end RowEnv

/-- **The gated chip has no `.row` gate**, so `chipParams`' `.row := ∅` provably erases nothing
    (contrast `GigaWitness`' warning about deploying `.row` empty on a 538-constraint chip). -/
theorem gatedIOProgAIR_no_row_constraints (m : ℕ) :
    ∀ c ∈ (gatedIOProgAIR m).constraints, c.kind ≠ Reified.ConstraintKind.row := by
  intro c hc
  simp only [gatedIOProgAIR, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

/-- The three row-domain memberships of the `n + 1`-row prefix deployment. -/
theorem chipRows_chipParams (D : OrbitDomain K) (coins : IOCoins K) (terminal : K) (N : ℕ)
    (hcap : N + 1 ≤ 2 ^ D.h) :
    ChipRows N (chipParams D coins terminal N) D.βcoset := by
  refine { boundary_mem := ?_, transition_mem := ?_, terminal_mem := ?_ }
  · have h0 : rowPt (chipParams D coins terminal N).ω D.βcoset 0 = D.βcoset := by
      rw [chipRowPt D coins terminal N 0, OrbitDomain.orbitPoint_zero]
    show rowPt (chipParams D coins terminal N).ω D.βcoset 0 ∈ D.boundaryDomain
    rw [h0]
    exact D.boundaryPoint_mem_boundaryDomain
  · intro i hi
    show rowPt (chipParams D coins terminal N).ω D.βcoset i
      ∈ D.transitionDomain (N + 1) (Nat.succ_pos N)
    rw [chipRowPt D coins terminal N i]
    exact D.orbitPoint_mem_transitionDomain (Nat.succ_pos N) hcap ⟨i, by omega⟩
      (show i + 1 < N + 1 from by omega)
  · show rowPt (chipParams D coins terminal N).ω D.βcoset N
      ∈ D.terminalDomain (N + 1) (Nat.succ_pos N)
    rw [chipRowPt D coins terminal N N, ← terminalPoint_succ D N]
    exact D.terminalPoint_mem_terminalDomain (N + 1) (Nat.succ_pos N)

/-- **The gated chip's core completeness: gated scalar columns give satisfying polynomial
    columns, on `N` transition rows with `N` unrelated to the number of records.**  This is the
    gated analogue of `IOChip.chip_satisfies` (`IOChipCompleteness.lean:304`), whose row count is
    forced to be `recsL.length`. -/
theorem gatedChip_satisfies (D : OrbitDomain K) (coins : IOCoins K) (terminal : K) (N : ℕ)
    (acc inv sel multInv : ℕ → K) (recs : ℕ → Fin m → K)
    (hcap : N + 1 ≤ 2 ^ D.h)
    (hgate : GatedIOAccepts N coins recs acc inv sel terminal) :
    (∀ k : Reified.ConstraintKind,
        ((chipParams D coins terminal N).rap (gatedIOProgAIR m) k).Satisfies
          (chipTrace D N acc inv sel multInv recs))
      ∧ ChipRows N (chipParams D coins terminal N) D.βcoset := by
  classical
  set q := chipParams D coins terminal N with hqdef
  set P := chipTrace D N acc inv sel multInv recs with hPdef
  have hacc : ∀ i, i < N + 1 → (rowEnv q D.βcoset P i).trace 0 = acc i :=
    fun i hi => chipTrace_acc D coins terminal acc inv sel multInv recs hcap i hi
  have hinv : ∀ i, i < N + 1 → (rowEnv q D.βcoset P i).trace 1 = inv i :=
    fun i hi => chipTrace_inv D coins terminal acc inv sel multInv recs hcap i hi
  have hsel : ∀ i, i < N + 1 → (rowEnv q D.βcoset P i).trace 2 = sel i :=
    fun i hi => chipTrace_mult D coins terminal acc inv sel multInv recs hcap i hi
  have hrec : ∀ i, i < N + 1 → ∀ c : Fin m,
      (rowEnv q D.βcoset P i).trace (4 + (c : ℕ)) = recs i c :=
    fun i hi c => chipTrace_rec D coins terminal acc inv sel multInv recs hcap i hi c
  -- the five scalar gate facts
  have gInit : ioAccInit.eval (rowEnv q D.βcoset P 0) = 0 := by
    rw [ioAccInit_eval_rowEnv, hacc 0 (by omega), hgate.init]
  have gTerm : ioTerm.eval (rowEnv q D.βcoset P N) = 0 := by
    rw [ioTerm_eval_rowEnv]
    have hp : q.pubVal 0 = terminal := rfl
    rw [hp, hacc N (by omega), hgate.term, sub_self]
  have gBool : ∀ i, i < N → ioSelBool.eval (rowEnv q D.βcoset P i) = 0 := by
    intro i hi
    rw [ioSelBool_eval_rowEnv, hsel i (by omega)]
    exact hgate.selBool i hi
  have gPin : ∀ i, i < N → (ioInvPinGated m 4).eval (rowEnv q D.βcoset P i) = 0 := by
    intro i hi
    have hg : q.chalVal 0 = coins.gamma := rfl
    have hpo : q.chalVal 1 = coins.pole := rfl
    rw [ioInvPinGated_eval_rowEnv q D.βcoset P i coins (recs i)
      (fun c => hrec i (by omega) c) hg hpo, hsel i (by omega), hinv i (by omega)]
    exact hgate.invPin i hi
  have gStep : ∀ i, i < N → ioSelAccStep.eval (rowEnv q D.βcoset P i) = 0 := by
    intro i hi
    rw [ioSelAccStep_eval_rowEnv, hacc (i + 1) (by omega), hacc i (by omega),
      hinv i (by omega), hsel i (by omega), hgate.step i hi]
    ring
  -- the three per-kind domains, read back as rows
  have hdb : ∀ x ∈ q.domain (.boundary : Reified.ConstraintKind),
      envOfTrace P q.ω x q.chalVal q.pubVal = rowEnv q D.βcoset P 0 := by
    intro x hx
    have hx1 : x = D.βcoset := by
      have : x ∈ D.boundaryDomain := hx
      simpa [OrbitDomain.boundaryDomain] using this
    have h0 : rowPt q.ω D.βcoset 0 = D.βcoset := by
      rw [chipRowPt D coins terminal N 0, OrbitDomain.orbitPoint_zero]
    rw [hx1, rowEnv, h0]
  have hdt : ∀ x ∈ q.domain (.transition : Reified.ConstraintKind),
      ∃ i, i < N ∧ envOfTrace P q.ω x q.chalVal q.pubVal = rowEnv q D.βcoset P i := by
    intro x hx
    have hx' : x ∈ D.transitionDomain (N + 1) (Nat.succ_pos N) := hx
    obtain ⟨i, hi, rfl⟩ :=
      (orbit_mem_transitionDomain_iff_active_nonterminal D (N + 1) (Nat.succ_pos N) hcap x).mp hx'
    refine ⟨(i : ℕ), by omega, ?_⟩
    rw [rowEnv, chipRowPt D coins terminal N (i : ℕ)]
  have hdm : ∀ x ∈ q.domain (.terminal : Reified.ConstraintKind),
      envOfTrace P q.ω x q.chalVal q.pubVal = rowEnv q D.βcoset P N := by
    intro x hx
    have hx' : x ∈ D.terminalDomain (N + 1) (Nat.succ_pos N) := hx
    have hxe : x = D.terminalPoint (N + 1) (Nat.succ_pos N) := by
      simpa [OrbitDomain.terminalDomain] using hx'
    have hn' : rowPt q.ω D.βcoset N = D.terminalPoint (N + 1) (Nat.succ_pos N) := by
      rw [chipRowPt D coins terminal N N, terminalPoint_succ D N]
    rw [hxe, rowEnv, hn']
  refine ⟨?_, chipRows_chipParams D coins terminal N hcap⟩
  refine (segmented_is_kinded (gatedIOProgAIR m) q.chalVal q.pubVal q.eDeg q.hExp q.ω
    q.βcoset q.βcoset_ne_zero q.hExp_pos q.domain P).mpr ?_
  intro c hc x hx
  simp only [gatedIOProgAIR, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · show ioAccInit.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
    rw [hdb x hx]; exact gInit
  · show ioSelBool.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
    obtain ⟨i, hi, he⟩ := hdt x hx
    rw [he]; exact gBool i hi
  · show (ioInvPinGated m 4).eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
    obtain ⟨i, hi, he⟩ := hdt x hx
    rw [he]; exact gPin i hi
  · show ioSelAccStep.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
    obtain ⟨i, hi, he⟩ := hdt x hx
    rw [he]; exact gStep i hi
  · show ioTerm.eval (envOfTrace P q.ω x q.chalVal q.pubVal) = 0
    rw [hdm x hx]; exact gTerm

/-! ### The headline: a satisfying trace with `n` real record rows and `N − n` padding rows -/

/-- **`padded_gated_satisfies` — padding rows are legal.**  For *any* total row count `N` at least
    the number of real records (and within the orbit's capacity), the gated chip admits committed
    polynomial columns satisfying its four per-kind ordinary RAPs, agreeing with the record list
    on the real rows, and reaching the **same terminal the unpadded chip reaches** — the honest
    LogUp sum `Σ_i 1/(pole + RLC^γ(rec i))`.  The padding rows carry the zero record and are
    subject to no denominator condition whatsoever: `hden` ranges over `recsL` only. -/
theorem padded_gated_satisfies (D : OrbitDomain K) (coins : IOCoins K)
    (recsL : List (Fin m → K)) (N : ℕ)
    (hle : recsL.length ≤ N) (hcap : N + 1 ≤ 2 ^ D.h)
    (hden : ∀ v ∈ recsL, compress coins v ≠ 0) :
    ∃ (terminal : K) (P : Fin (gatedIOProgAIR m).numTraceCols → K[X]),
        (∀ k : Reified.ConstraintKind,
            ((chipParams D coins terminal N).rap (gatedIOProgAIR m) k).Satisfies P)
      ∧ ChipRows N (chipParams D coins terminal N) D.βcoset
      ∧ ChipAgreement recsL coins terminal (chipParams D coins terminal N) D.βcoset P
      ∧ (∀ i, i < N → ∀ c : Fin m,
          (rowEnv (chipParams D coins terminal N) D.βcoset P i).trace (4 + (c : ℕ))
            = listCol recsL i c)
      ∧ (∀ i, i < N →
          ((rowEnv (chipParams D coins terminal N) D.βcoset P i).trace 2 = 1
            ↔ i < recsL.length))
      ∧ terminal = ∑ i : Fin recsL.length, (compress coins (recsL.get i))⁻¹ := by
  classical
  set n := recsL.length with hn
  set g : ℕ → K := fun i => (compress coins (listCol recsL i))⁻¹ with hg
  set sel : ℕ → K := fun i => if i < n then 1 else 0 with hsel
  set acc : ℕ → K := fun j => ∑ i ∈ Finset.range j, sel i * g i with haccdef
  have hgate : GatedIOAccepts N coins (listCol recsL) acc g sel (acc N) := by
    refine { init := ?_, selBool := ?_, invPin := ?_, step := ?_, term := rfl }
    · simp [haccdef]
    · intro i _
      by_cases hi : i < n
      · simp only [hsel, if_pos hi]; ring
      · simp only [hsel, if_neg hi]; ring
    · intro i _
      by_cases hi : i < n
      · have hne : compress coins (listCol recsL i) ≠ 0 := by
          rw [show listCol recsL i = recsL.get ⟨i, hi⟩ from listCol_get recsL ⟨i, hi⟩]
          exact hden _ (List.get_mem _ _)
        simp only [hsel, if_pos hi, one_mul, hg]
        rw [mul_inv_cancel₀ hne, sub_self]
      · simp only [hsel, if_neg hi, zero_mul]
    · intro i _
      show (∑ k ∈ Finset.range (i + 1), sel k * g k)
        = (∑ k ∈ Finset.range i, sel k * g k) + sel i * g i
      exact Finset.sum_range_succ _ _
  obtain ⟨hsat, hrows⟩ :=
    gatedChip_satisfies D coins (acc N) N acc g sel (fun _ => 1) (listCol recsL) hcap hgate
  have hread : ∀ i, i < N + 1 → ∀ c : Fin m,
      (rowEnv (chipParams D coins (acc N) N) D.βcoset
        (chipTrace D N acc g sel (fun _ => 1) (listCol recsL)) i).trace (4 + (c : ℕ))
        = listCol recsL i c :=
    fun i hi c => chipTrace_rec D coins (acc N) acc g sel (fun _ => 1) (listCol recsL) hcap i hi c
  have hagree : ChipAgreement recsL coins (acc N) (chipParams D coins (acc N) N) D.βcoset
      (chipTrace D N acc g sel (fun _ => 1) (listCol recsL)) := by
    refine { gamma_eq := rfl, pole_eq := rfl, terminal_eq := rfl, record_eq := ?_ }
    intro i c
    have hi : (i : ℕ) < N + 1 := by have := i.isLt; omega
    rw [hread (i : ℕ) hi c, listCol_get]
  -- the terminal is the honest sum over the real records only
  have hsum : acc N = ∑ i : Fin recsL.length, (compress coins (recsL.get i))⁻¹ := by
    have h1 : (∑ i ∈ Finset.range n, sel i * g i) = ∑ i ∈ Finset.range N, sel i * g i := by
      have hsub : Finset.range n ⊆ Finset.range N := by
        intro x hx
        exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hle)
      refine Finset.sum_subset hsub (fun x _ hx => ?_)
      have hxn : ¬ x < n := fun h => hx (Finset.mem_range.mpr h)
      simp only [hsel, if_neg hxn, zero_mul]
    have h2 : (∑ i ∈ Finset.range n, sel i * g i) = ∑ i ∈ Finset.range n, g i := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [hsel]
      simp only [if_pos (Finset.mem_range.mp hx), one_mul]
    have h3 : (∑ i ∈ Finset.range n, g i)
        = ∑ i : Fin recsL.length, (compress coins (recsL.get i))⁻¹ := by
      rw [hn, Finset.sum_range]
      exact Finset.sum_congr rfl (fun i _ => by rw [hg]; simp only [listCol_get])
    show (∑ i ∈ Finset.range N, sel i * g i) = _
    rw [← h1, h2, h3]
  have hselread : ∀ i, i < N →
      ((rowEnv (chipParams D coins (acc N) N) D.βcoset
          (chipTrace D N acc g sel (fun _ => 1) (listCol recsL)) i).trace 2 = 1
        ↔ i < recsL.length) := by
    intro i hi
    rw [chipTrace_mult D coins (acc N) acc g sel (fun _ => 1) (listCol recsL) hcap i (by omega)]
    by_cases hin : i < n
    · have hs1 : sel i = 1 := by simp only [hsel]; exact if_pos hin
      rw [hs1]
      exact ⟨fun _ => hin, fun _ => rfl⟩
    · have hs0 : sel i = 0 := by simp only [hsel]; exact if_neg hin
      rw [hs0]
      exact ⟨fun h => absurd h zero_ne_one, fun h => absurd h hin⟩
  exact ⟨acc N, chipTrace D N acc g sel (fun _ => 1) (listCol recsL), hsat, hrows, hagree,
    (fun i hi c => hread i (by omega) c), hselread, hsum⟩

/-! ## 7.

This is the measurement the observation in `JN` §6 asked for, and it comes out *stronger* than
the observation: it is not merely that a padding row needs an invertible compressed denominator,
it is that **every** transition row of the ungated request chip strictly moves the accumulator.
So there is no such thing as an inert row, whatever the prover commits there.

Note the hypothesis bundle: no record list, no agreement, no coin condition.  Satisfaction of the
ungated chip's per-kind RAPs on the `N + 1`-row prefix deployment is the whole input. -/

/-- **Scalar form.**  The ungated inverse pin forces `inv i ≠ 0`, and the ungated accumulation
    step adds it, so the accumulator moves at every one of the `N` rows. -/
theorem ungated_row_moves (coins : IOCoins K) (recs : ℕ → Fin m → K) (acc inv : ℕ → K) (N : ℕ)
    (hpin : ∀ i, i < N → compress coins (recs i) * inv i = 1)
    (hstep : ∀ i, i < N → acc (i + 1) = acc i + inv i) :
    ∀ i, i < N → acc (i + 1) ≠ acc i := by
  intro i hi hcon
  have hne : inv i ≠ 0 := right_ne_zero_of_mul_eq_one (hpin i hi)
  apply hne
  have h1 := hstep i hi
  rw [hcon] at h1
  exact add_left_cancel (show acc i + inv i = acc i + 0 by rw [add_zero]; exact h1.symm)

/-- **`ungated_no_inert_row` — AIR form, no side hypotheses.**  Any committed trace satisfying the
    *ungated* `finiteIOProgAIR` at the `N + 1`-row prefix deployment moves its accumulator column
    at every transition row.  Hence a padded deployment of the ungated chip is impossible: the
    padding rows would have to change the terminal. -/
theorem ungated_no_inert_row (D : OrbitDomain K) (coins : IOCoins K) (terminal : K) (N : ℕ)
    (hcap : N + 1 ≤ 2 ^ D.h)
    (P : Fin (finiteIOProgAIR m).numTraceCols → K[X])
    (hsat : ∀ k : Reified.ConstraintKind,
      ((chipParams D coins terminal N).rap (finiteIOProgAIR m) k).Satisfies P) :
    ∀ i, i < N →
      (rowEnv (chipParams D coins terminal N) D.βcoset P (i + 1)).trace 0
        ≠ (rowEnv (chipParams D coins terminal N) D.βcoset P i).trace 0 := by
  classical
  set q := chipParams D coins terminal N with hqdef
  have hrows := chipRows_chipParams D coins terminal N hcap
  have hg := gates_vanish_of_satisfies q (finiteIOProgAIR m) P hsat
  have hmPpin : (⟨.transition, ioInvPin m 4⟩ : Constraint) ∈ (finiteIOProgAIR m).constraints := by
    simp [finiteIOProgAIR]
  have hmPstep : (⟨.transition, ioProgAccStep⟩ : Constraint) ∈
      (finiteIOProgAIR m).constraints := by simp [finiteIOProgAIR]
  intro i hi hcon
  -- the inverse pin at row `i`, with the record read off the trace itself
  have hpin := hg _ hmPpin (rowPt q.ω D.βcoset i) (hrows.transition_mem i hi)
  rw [show (envOfTrace P q.ω (rowPt q.ω D.βcoset i) q.chalVal q.pubVal)
      = rowEnv q D.βcoset P i from rfl,
    ioInvPin_eval_rowEnv q D.βcoset P i coins
      (fun c : Fin m => (rowEnv q D.βcoset P i).trace (4 + (c : ℕ)))
      (fun _ => rfl) rfl rfl, sub_eq_zero] at hpin
  have hinvne : (rowEnv q D.βcoset P i).trace 1 ≠ 0 := right_ne_zero_of_mul_eq_one hpin
  have hstep := hg _ hmPstep (rowPt q.ω D.βcoset i) (hrows.transition_mem i hi)
  rw [show (envOfTrace P q.ω (rowPt q.ω D.βcoset i) q.chalVal q.pubVal)
      = rowEnv q D.βcoset P i from rfl,
    ioProgAccStep_eval_rowEnv, sub_sub, sub_eq_zero] at hstep
  rw [hcon] at hstep
  exact hinvne (add_left_cancel
    (show (rowEnv q D.βcoset P i).trace 0 + (rowEnv q D.βcoset P i).trace 1
        = (rowEnv q D.βcoset P i).trace 0 + 0 by rw [add_zero]; exact hstep.symm))


/-! ## 8. Non-vacuity over a concrete field, with genuine padding rows

The tree's standard is `IOChipCompleteness.satisfies_of_io_lio_concrete` (`:692`) and
`GigaWitness.giga_bundle_concrete` (`:878`), both hypothesis-free over `ZMod 97`.  Their orbit
(`IOChipCompleteness.concreteOrbit`) has `h = 1`, i.e. capacity `2`, which is exactly one record
row plus the terminal row — no room for a padding row.  So a fourth-order orbit is needed:
`22 ∈ ZMod 97` has `22² = −1`, hence order `4 = 2²`.

`gated_padding_concrete` then takes **no hypotheses at all** and exhibits a chip with `1` real
record row, `2` padding rows and the terminal row, reaching the honest terminal `1`.  The padding
rows carry the zero record, whose compressed denominator at these coins is `1`; but the point is
that no gate looks at it — `padded_gated_satisfies`' `hden` ranges over the record *list* only. -/

section Concrete

local instance factPrime97gated : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- `22² = −1` in `ZMod 97`, so `22` has multiplicative order `4 = 2²`. -/
theorem order_twentytwo : orderOf (22 : ZMod 97) = 2 ^ 2 :=
  orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)

/-- A concrete four-row orbit domain over `ZMod 97` — room for one record row, two padding rows
    and the terminal row. -/
noncomputable def concreteOrbit4 : OrbitDomain (ZMod 97) where
  h := 2
  ω := 22
  βcoset := 1
  βcoset_ne_zero := one_ne_zero
  order_ω := order_twentytwo

@[simp] theorem concreteOrbit4_h : concreteOrbit4.h = 2 := rfl

/-- **`gated_padding_concrete` — padding rows are legal, with no hypotheses.**  Over `ZMod 97`, at
    coins `(γ, pole) = (0, 1)` and the single zero record, the gated chip is satisfied on a
    deployment with **three** transition rows of which only the first is a record row, and its
    terminal is the honest one-record LogUp sum `1`. -/
theorem gated_padding_concrete :
    ∃ (terminal : ZMod 97) (P : Fin (gatedIOProgAIR 1).numTraceCols → (ZMod 97)[X]),
        (∀ k : Reified.ConstraintKind,
            ((chipParams concreteOrbit4 ⟨0, 1⟩ terminal 3).rap (gatedIOProgAIR 1) k).Satisfies P)
      ∧ ChipRows 3 (chipParams concreteOrbit4 ⟨0, 1⟩ terminal 3) concreteOrbit4.βcoset
      ∧ ChipAgreement [(0 : Fin 1 → ZMod 97)] ⟨0, 1⟩ terminal
          (chipParams concreteOrbit4 ⟨0, 1⟩ terminal 3) concreteOrbit4.βcoset P
      ∧ terminal = 1 := by
  have hc : compress (⟨0, 1⟩ : IOCoins (ZMod 97)) (0 : Fin 1 → ZMod 97) = 1 := by
    show (1 : ZMod 97) + Walk.rlc (0 : ZMod 97) (0 : Fin 1 → ZMod 97) = 1
    rw [show Walk.rlc (0 : ZMod 97) (0 : Fin 1 → ZMod 97) = 0 from by simp [Walk.rlc], add_zero]
  have hden : ∀ v ∈ ([(0 : Fin 1 → ZMod 97)] : List (Fin 1 → ZMod 97)),
      compress (⟨0, 1⟩ : IOCoins (ZMod 97)) v ≠ 0 := by
    intro v hv
    have hv0 : v = 0 := by simpa using hv
    rw [hv0, hc]
    exact one_ne_zero
  have hcap : (3 : ℕ) + 1 ≤ 2 ^ concreteOrbit4.h := by
    rw [concreteOrbit4_h]
    norm_num
  obtain ⟨t, P, hsat, hrows, hag, _, _, hsum⟩ :=
    padded_gated_satisfies concreteOrbit4 (⟨0, 1⟩ : IOCoins (ZMod 97))
      [(0 : Fin 1 → ZMod 97)] 3 (by simp) hcap hden
  refine ⟨t, P, hsat, hrows, hag, ?_⟩
  rw [hsum]
  show (∑ _i : Fin 1, (compress (⟨0, 1⟩ : IOCoins (ZMod 97)) (0 : Fin 1 → ZMod 97))⁻¹) = 1
  rw [Finset.sum_const, hc, inv_one]
  simp

end Concrete

/-! ## 9. Stage 2 — how far the padded deployment gets, and where it stops

`GigaWitness.gigaParams_domain_eq_computeDomain` (`GigaRAPAssembledWitness.lean:1026`) closes the
compute/IO domain reconciliation *given* `hn : n + 1 = cfg.compRows`.

**Padding is the wrong direction.**  Every compute row emits at
least one memory request: the paper is an unconditional
`((input_formula, formula_tail), 3, ln_prev·z) = mem_record₁` at the top of Algorithm
`NockCompute`, before any branch, and in this tree `NockVM.activeRequestRecords`
(`Nock/NockVM.lean:650`) returns a nonempty list in all eleven compute states.  Hence

    cfg.compRows ≤ |derivedRequestIO|

for **every** execution, so `|requests| + 1 = cfg.compRows` is not merely unproved, it is *false*
(§9.2), and `|requests| ≤ cfg.compRows − 1` — what a padded one-record-per-row deployment needs —
is false too.  The prog-IO chip needs *more* rows than the compute table, not fewer.

What the paper does instead is visible at the paper: its IO block is
`IO_prog(i,k,·)` for `k ∈ [1 … regs(l)]` — up to `M_IO` records **per row**, with
the paper noting "exactly the first `regs(op) ≤ M_IO` memory records are non-zero per
opcode" and the paper zeroing the unused ones.  So the paper's row can
absorb the three records of an OP6/OP9 row.  This tree's chip carries one width-`m` record per
row.  Reconciling the two row counts therefore needs **both** ingredients: multi-record rows (to
fit `≥ compRows` records into `compRows` rows) *and* the selector of this module (to make the
rows with `regs = 0` inert).  Only the second is built here.

The third obstruction, independent of both, is structural: `GigaChips.finiteComputeChip`
(`GigaRAPIOSlots.lean:631`) is fixed to `computeCombinedFiniteAIR 10 8 S.map`
(`NockGigaRAPFinite.lean:186`), whose IO block is literally `finiteIOProgAIR m` — the *ungated*
chip.  Substituting `gatedIOProgAIR` there is a new combined AIR with its own `varsBelow`,
census, degree and `satisfies_iff_kinded` proofs, and the result would no longer be the chip
`GigaRAPIOSlots.io_lio_of_giga_satisfies_at_production_coins` consumes.  That is why this module
stops at the standalone chip. -/

section Stage2

/-! ### 9.1 The shared-domain equation, discharged by construction -/

/-- The padded row count fits the certified orbit — no hypothesis. -/
theorem padded_capacity {F K : Type*} [Field F] [Field K] [Algebra F K]
    (cfg : ExactConfig F K) : (cfg.compRows - 1) + 1 ≤ 2 ^ cfg.orbit.h := by
  have h1 := cfg.compRows_pos
  have h2 := cfg.compRows_le
  omega

/-- **`gigaParams_domain_eq_computeDomain`'s hypothesis, discharged.**  At the padded row count
    `cfg.compRows − 1` the assembled deployment's four per-kind domains *are* `cfg.computeDomain`,
    with no assumption at all. -/
theorem gated_padded_domain_eq_computeDomain {F K : Type*} [Field F] [Field K] [Algebra F K]
    (cfg : ExactConfig F K) (coins : IOCoins K) (terminal : K) :
    (GigaWitness.gigaParams cfg.orbit coins terminal (cfg.compRows - 1)).domain
      = cfg.computeDomain :=
  GigaWitness.gigaParams_domain_eq_computeDomain cfg coins terminal (cfg.compRows - 1)
    (by have := cfg.compRows_pos; omega)

/-! ### 9.2 But the request list never fits: `|requests| ≥ compRows` -/

/-- A list whose blocks are all nonempty is at least as long as the list of blocks. -/
theorem length_le_flatMap {α β : Type*} (l : List α) (g : α → List β)
    (hg : ∀ a ∈ l, g a ≠ []) : l.length ≤ (l.flatMap g).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h1 : 1 ≤ (g a).length := List.length_pos_of_ne_nil (hg a (by simp))
    have h2 : t.length ≤ (t.flatMap g).length := ih (fun b hb => hg b (List.mem_cons_of_mem a hb))
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    omega

/-- **Every compute row emits at least one memory request** — the paper's unconditional
    `mem_record₁`, realized in this tree as a nonempty `activeRequestRecords` in all eleven
    compute states. -/
theorem activeRequestRecords_ne_nil {K : Type*} (pub : ComputeTable.Pub K) :
    NockVM.activeRequestRecords pub ≠ [] := by
  cases hs : pub.state <;> simp [NockVM.activeRequestRecords, hs]

/-- **`compRows_le_requests_length`.**  The derived request list is at least as long as the
    compute table. -/
theorem compRows_le_requests_length {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    cfg.compRows ≤ exec.derivedRequestIO.length := by
  rw [ExactExecution.derivedRequestIO_eq_computeRows, List.length_map,
    ← exec.computeRows_length]
  exact length_le_flatMap exec.computeRows _ (fun row _ => activeRequestRecords_ne_nil _)

/-- **The row-count equation the assembled route wanted is false for every execution.** -/
theorem requests_row_count_ne {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.derivedRequestIO.length + 1 ≠ cfg.compRows := by
  have := compRows_le_requests_length exec
  omega

/-- **And padding is the wrong direction.**  A one-record-per-row padded deployment on
    `cfg.compRows` rows would need `|requests| ≤ cfg.compRows − 1`; no execution satisfies that. -/
theorem padding_does_not_fit {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    ¬ (exec.derivedRequestIO.length ≤ cfg.compRows - 1) := by
  have h1 := compRows_le_requests_length exec
  have h2 := cfg.compRows_pos
  omega

end Stage2


/-! ## 10. The gated analogue of `io_lio_of_satisfies`

`IOChipSoundness.io_lio_of_satisfies` (`IOChipSoundness.lean:408`) takes hostile committed traces
for both ungated chips and returns `IO.LIO`.  This section is its gated counterpart on the
request side, and it makes the extra hypothesis visible in the signature: `hsel`, the selector
pin.  §5 is why that hypothesis cannot be removed, and §3 is why the paper has it for free.

The response side is unchanged — `finiteIOMemAIR` is used verbatim, and its four branches are the
ones `projWitness_accepts` already discharges. -/

section GatedSound

/-- **Hostile gated columns give `GatedIOAccepts`.**  Every column is read off the committed
    trace; only the record identification (`hrec`) is carried, exactly as
    `ChipAgreement.record_eq` carries it for the ungated chip. -/
theorem gated_accepts_of_satisfies (D : OrbitDomain K) (coins : IOCoins K) (terminal : K)
    (N : ℕ) (hcap : N + 1 ≤ 2 ^ D.h) (recs : ℕ → Fin m → K)
    (Pp : Fin (gatedIOProgAIR m).numTraceCols → K[X])
    (hsat : ∀ k : Reified.ConstraintKind,
      ((chipParams D coins terminal N).rap (gatedIOProgAIR m) k).Satisfies Pp)
    (hrec : ∀ i, i < N → ∀ c : Fin m,
      (rowEnv (chipParams D coins terminal N) D.βcoset Pp i).trace (4 + (c : ℕ)) = recs i c) :
    GatedIOAccepts N coins recs
      (fun i => (rowEnv (chipParams D coins terminal N) D.βcoset Pp i).trace 0)
      (fun i => (rowEnv (chipParams D coins terminal N) D.βcoset Pp i).trace 1)
      (fun i => (rowEnv (chipParams D coins terminal N) D.βcoset Pp i).trace 2)
      terminal := by
  classical
  set q := chipParams D coins terminal N with hqdef
  have hrows := chipRows_chipParams D coins terminal N hcap
  have hg := gates_vanish_of_satisfies q (gatedIOProgAIR m) Pp hsat
  have hmInit : (⟨.boundary, ioAccInit⟩ : Constraint) ∈ (gatedIOProgAIR m).constraints := by
    simp [gatedIOProgAIR]
  have hmBool : (⟨.transition, ioSelBool⟩ : Constraint) ∈ (gatedIOProgAIR m).constraints := by
    simp [gatedIOProgAIR]
  have hmPin : (⟨.transition, ioInvPinGated m 4⟩ : Constraint) ∈
      (gatedIOProgAIR m).constraints := by simp [gatedIOProgAIR]
  have hmStep : (⟨.transition, ioSelAccStep⟩ : Constraint) ∈
      (gatedIOProgAIR m).constraints := by simp [gatedIOProgAIR]
  have hmTerm : (⟨.terminal, ioTerm⟩ : Constraint) ∈ (gatedIOProgAIR m).constraints := by
    simp [gatedIOProgAIR]
  refine { init := ?_, selBool := ?_, invPin := ?_, step := ?_, term := ?_ }
  · have h := hg _ hmInit (rowPt q.ω D.βcoset 0) hrows.boundary_mem
    rw [show (envOfTrace Pp q.ω (rowPt q.ω D.βcoset 0) q.chalVal q.pubVal)
        = rowEnv q D.βcoset Pp 0 from rfl, ioAccInit_eval_rowEnv] at h
    exact h
  · intro i hi
    have h := hg _ hmBool (rowPt q.ω D.βcoset i) (hrows.transition_mem i hi)
    rw [show (envOfTrace Pp q.ω (rowPt q.ω D.βcoset i) q.chalVal q.pubVal)
        = rowEnv q D.βcoset Pp i from rfl, ioSelBool_eval_rowEnv] at h
    exact h
  · intro i hi
    have h := hg _ hmPin (rowPt q.ω D.βcoset i) (hrows.transition_mem i hi)
    rw [show (envOfTrace Pp q.ω (rowPt q.ω D.βcoset i) q.chalVal q.pubVal)
        = rowEnv q D.βcoset Pp i from rfl,
      ioInvPinGated_eval_rowEnv q D.βcoset Pp i coins (recs i) (hrec i hi) rfl rfl] at h
    exact h
  · intro i hi
    have h := hg _ hmStep (rowPt q.ω D.βcoset i) (hrows.transition_mem i hi)
    rw [show (envOfTrace Pp q.ω (rowPt q.ω D.βcoset i) q.chalVal q.pubVal)
        = rowEnv q D.βcoset Pp i from rfl, ioSelAccStep_eval_rowEnv, sub_sub, sub_eq_zero] at h
    exact h
  · have h := hg _ hmTerm (rowPt q.ω D.βcoset N) hrows.terminal_mem
    rw [show (envOfTrace Pp q.ω (rowPt q.ω D.βcoset N) q.chalVal q.pubVal)
        = rowEnv q D.βcoset Pp N from rfl, ioTerm_eval_rowEnv,
      show q.pubVal 0 = terminal from rfl, sub_eq_zero] at h
    exact h.symm

variable (records : PreChallengeRecords K m) (coins : IOCoins K) (terminal : K)
  (D : OrbitDomain K) (N : ℕ) (qm : SegmentedRAPParams K) (x₀m : K)
  (Pp : Fin (gatedIOProgAIR m).numTraceCols → K[X])
  (Pm : Fin (finiteIOMemAIR m).numTraceCols → K[X])

/-- **`gated_projWitness_accepts` — `FiniteIOAccepts` from a *padded, gated* request chip and the
    unchanged response chip.**

The request chip is deployed on `N` transition rows with `N` at least — and typically strictly
greater than — the number of records, which is exactly what the ungated chip cannot do
(`ungated_no_inert_row`).  The extra hypothesis relative to
`IOChipSoundness.projWitness_accepts` is `hsel`, the selector pin; `hnN` is the row budget. -/
theorem gated_projWitness_accepts
    (hcap : N + 1 ≤ 2 ^ D.h)
    (hsatP : ∀ k : Reified.ConstraintKind,
      ((chipParams D coins terminal N).rap (gatedIOProgAIR m) k).Satisfies Pp)
    (hsatM : ∀ k : Reified.ConstraintKind, (qm.rap (finiteIOMemAIR m) k).Satisfies Pm)
    (hrowsM : ChipRows records.responses.length qm x₀m)
    (hagM : ChipAgreement records.responses coins terminal qm x₀m Pm)
    (hnN : records.requests.length ≤ N)
    (hrecP : ∀ i, i < N → ∀ c : Fin m,
      (rowEnv (chipParams D coins terminal N) D.βcoset Pp i).trace (4 + (c : ℕ))
        = listCol records.requests i c)
    (hsel : ∀ i, i < N →
      ((rowEnv (chipParams D coins terminal N) D.βcoset Pp i).trace 2 = 1
        ↔ i < records.requests.length)) :
    FiniteIOAccepts records coins
      (projWitness records coins terminal (chipParams D coins terminal N) qm D.βcoset x₀m
        Pp Pm) := by
  classical
  have hgated := gated_accepts_of_satisfies D coins terminal N hcap
    (listCol records.requests) Pp hsatP hrecP
  obtain ⟨hinit, hpin, hstep, hterm⟩ :=
    hgated.ungated_of_selected_prefix records.requests.length hnN hsel
  -- the response side is the existing ungated argument, verbatim
  have hM := gates_vanish_of_satisfies qm (finiteIOMemAIR m) Pm hsatM
  have hmMpin : (⟨.transition, ioInvPin m 4⟩ : Constraint) ∈ (finiteIOMemAIR m).constraints := by
    simp [finiteIOMemAIR]
  have hmMbool : (⟨.transition, ioMultBool⟩ : Constraint) ∈ (finiteIOMemAIR m).constraints := by
    simp [finiteIOMemAIR]
  have hmMminv : (⟨.transition, ioMultInvPin⟩ : Constraint) ∈
      (finiteIOMemAIR m).constraints := by simp [finiteIOMemAIR]
  have hmMinit : (⟨.boundary, ioAccInit⟩ : Constraint) ∈ (finiteIOMemAIR m).constraints := by
    simp [finiteIOMemAIR]
  have hmMstep : (⟨.transition, ioMemAccStep⟩ : Constraint) ∈
      (finiteIOMemAIR m).constraints := by simp [finiteIOMemAIR]
  have hmMterm : (⟨.terminal, ioTerm⟩ : Constraint) ∈ (finiteIOMemAIR m).constraints := by
    simp [finiteIOMemAIR]
  refine
    { requestInvPin := ?_, responseInvPin := ?_, multBool := ?_, multInvPin := ?_,
      requestInit := ?_, requestStep := ?_, responseInit := ?_, responseStep := ?_,
      requestTerm := ?_, responseTerm := ?_ }
  · intro i
    have h := hpin (i : ℕ) i.isLt
    rwa [listCol_get] at h
  · intro j
    have h := hM _ hmMpin (rowPt qm.ω x₀m (j : ℕ)) (hrowsM.transition_mem j j.isLt)
    rw [show (envOfTrace Pm qm.ω (rowPt qm.ω x₀m (j : ℕ)) qm.chalVal qm.pubVal)
        = rowEnv qm x₀m Pm (j : ℕ) from rfl,
      ioInvPin_eval_rowEnv qm x₀m Pm (j : ℕ) coins (records.responses.get j)
        (hagM.record_eq j) hagM.gamma_eq hagM.pole_eq, sub_eq_zero] at h
    exact h
  · intro j
    have h := hM _ hmMbool (rowPt qm.ω x₀m (j : ℕ)) (hrowsM.transition_mem j j.isLt)
    rw [show (envOfTrace Pm qm.ω (rowPt qm.ω x₀m (j : ℕ)) qm.chalVal qm.pubVal)
        = rowEnv qm x₀m Pm (j : ℕ) from rfl, ioMultBool_eval_rowEnv] at h
    exact h
  · intro j
    have h := hM _ hmMminv (rowPt qm.ω x₀m (j : ℕ)) (hrowsM.transition_mem j j.isLt)
    rw [show (envOfTrace Pm qm.ω (rowPt qm.ω x₀m (j : ℕ)) qm.chalVal qm.pubVal)
        = rowEnv qm x₀m Pm (j : ℕ) from rfl, ioMultInvPin_eval_rowEnv, sub_eq_zero] at h
    exact h
  · exact hinit
  · intro i
    exact hstep (i : ℕ) i.isLt
  · have h := hM _ hmMinit (rowPt qm.ω x₀m 0) hrowsM.boundary_mem
    rw [show (envOfTrace Pm qm.ω (rowPt qm.ω x₀m 0) qm.chalVal qm.pubVal)
        = rowEnv qm x₀m Pm 0 from rfl, ioAccInit_eval_rowEnv] at h
    exact h
  · intro j
    have h := hM _ hmMstep (rowPt qm.ω x₀m (j : ℕ)) (hrowsM.transition_mem j j.isLt)
    rw [show (envOfTrace Pm qm.ω (rowPt qm.ω x₀m (j : ℕ)) qm.chalVal qm.pubVal)
        = rowEnv qm x₀m Pm (j : ℕ) from rfl, ioMemAccStep_eval_rowEnv,
      sub_sub, sub_eq_zero] at h
    simp only [projWitness, Fin.val_succ, Fin.val_castSucc]
    exact h
  · exact hterm
  · have h := hM _ hmMterm (rowPt qm.ω x₀m records.responses.length) hrowsM.terminal_mem
    rw [show (envOfTrace Pm qm.ω (rowPt qm.ω x₀m records.responses.length) qm.chalVal qm.pubVal)
        = rowEnv qm x₀m Pm records.responses.length from rfl, ioTerm_eval_rowEnv,
      hagM.terminal_eq, sub_eq_zero] at h
    simp only [projWitness, Fin.val_last]
    exact h.symm

/-- **`gated_io_lio_of_satisfies` — the gated analogue of `IOChipSoundness.io_lio_of_satisfies`
    (`IOChipSoundness.lean:408`).**  Identical conclusion and identical five counted-event / range
    side conditions; the request chip is now the selector-gated one on `N ≥ |requests|` rows, at
    the price of the selector pin `hsel`. -/
theorem gated_io_lio_of_satisfies [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p] {Ksz : ℕ}
    (hcap : N + 1 ≤ 2 ^ D.h)
    (hsatP : ∀ k : Reified.ConstraintKind,
      ((chipParams D coins terminal N).rap (gatedIOProgAIR m) k).Satisfies Pp)
    (hsatM : ∀ k : Reified.ConstraintKind, (qm.rap (finiteIOMemAIR m) k).Satisfies Pm)
    (hrowsM : ChipRows records.responses.length qm x₀m)
    (hagM : ChipAgreement records.responses coins terminal qm x₀m Pm)
    (hnN : records.requests.length ≤ N)
    (hrecP : ∀ i, i < N → ∀ c : Fin m,
      (rowEnv (chipParams D coins terminal N) D.βcoset Pp i).trace (4 + (c : ℕ))
        = listCol records.requests i c)
    (hsel : ∀ i, i < N →
      ((rowEnv (chipParams D coins terminal N) D.βcoset Pp i).trace 2 = 1
        ↔ i < records.requests.length))
    (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz records.requests.length)
    (hKresp : records.responses.length ≤ Ksz)
    (hreqnd : records.requests.Nodup) (hrespnd : records.responses.Nodup)
    (hγ : coins.gamma ∉ IORLCCollisionEvent records)
    (hpole : coins.pole ∉ IOLogDerivEvent records coins.gamma) :
    IO.LIO Ksz records.requests records.responses :=
  finiteIO_sound
    (gated_projWitness_accepts records coins terminal D N qm x₀m Pp Pm hcap hsatP hsatM
      hrowsM hagM hnN hrecP hsel)
    hKp hKreq hKresp hreqnd hrespnd hγ hpole

end GatedSound


/-! ## 11. The gated soundness hypothesis bundle is inhabited, with real padding

`IOChipSoundness.hypotheses_inhabited` (`:555`) shows the *ungated* soundness theorem's trace-side
hypotheses can hold at once, at a one-record two-row deployment.  This is its gated counterpart,
and it is the one thing the ungated chip provably cannot do: the request chip runs on **three**
transition rows carrying **one** record, which `ungated_no_inert_row` forbids for
`finiteIOProgAIR`.  No hypotheses; concrete over `ZMod 97`. -/

section ConcreteSound

local instance factPrime97sound : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- The padded request accumulator: `0` on the first row, `1` from then on. -/
def padAcc : ℕ → ZMod 97 := fun i => if i = 0 then 0 else 1
/-- The committed reciprocal column: constantly `1` (the compressed denominator is `1`). -/
def padInv : ℕ → ZMod 97 := fun _ => 1
/-- The selector: on for row `0`, **off for the two padding rows**. -/
def padSel : ℕ → ZMod 97 := fun i => if i < 1 then 1 else 0

theorem compress_zero_rec :
    compress (⟨0, 1⟩ : IOCoins (ZMod 97)) (0 : Fin 1 → ZMod 97) = 1 := by
  show (1 : ZMod 97) + Walk.rlc (0 : ZMod 97) (0 : Fin 1 → ZMod 97) = 1
  rw [show Walk.rlc (0 : ZMod 97) (0 : Fin 1 → ZMod 97) = 0 from by simp [Walk.rlc], add_zero]

theorem listCol_rec1 (i : ℕ) : listCol ([(0 : Fin 1 → ZMod 97)]) i = 0 := by
  by_cases h : i < 1
  · have hi0 : i = 0 := by omega
    subst hi0
    rw [listCol_get ([(0 : Fin 1 → ZMod 97)]) ⟨0, by simp⟩]
    rfl
  · rw [listCol, dif_neg (by simpa using h)]

theorem padGate : GatedIOAccepts 3 (⟨0, 1⟩ : IOCoins (ZMod 97))
    (listCol [(0 : Fin 1 → ZMod 97)]) padAcc padInv padSel 1 := by
  refine { init := ?_, selBool := ?_, invPin := ?_, step := ?_, term := ?_ }
  · norm_num [padAcc]
  · intro i _
    by_cases h : i < 1 <;> simp [padSel, h]
  · intro i _
    rw [listCol_rec1, compress_zero_rec]
    by_cases h : i < 1 <;> simp [padSel, padInv, h]
  · intro i hi
    interval_cases i <;> norm_num [padAcc, padSel, padInv]
  · norm_num [padAcc]

/-- **`gated_sound_hypotheses_inhabited` — the trace-side hypotheses of
    `gated_io_lio_of_satisfies` hold simultaneously, with two genuine padding rows.**  Take no
    hypotheses; over `ZMod 97` on `concreteOrbit4`, at the one-request/one-response record pair,
    the request chip is deployed on `3` transition rows and the response chip on `1`. -/
theorem gated_sound_hypotheses_inhabited :
    ∃ (Pp : Fin (gatedIOProgAIR 1).numTraceCols → (ZMod 97)[X])
      (Pm : Fin (finiteIOMemAIR 1).numTraceCols → (ZMod 97)[X]),
      (3 : ℕ) + 1 ≤ 2 ^ concreteOrbit4.h
      ∧ (∀ k : Reified.ConstraintKind,
          ((chipParams concreteOrbit4 (⟨0, 1⟩ : IOCoins (ZMod 97)) 1 3).rap
            (gatedIOProgAIR 1) k).Satisfies Pp)
      ∧ (∀ k : Reified.ConstraintKind,
          ((chipParams concreteOrbit4 (⟨0, 1⟩ : IOCoins (ZMod 97)) 1 1).rap
            (finiteIOMemAIR 1) k).Satisfies Pm)
      ∧ ChipRows ([(0 : Fin 1 → ZMod 97)]).length
          (chipParams concreteOrbit4 (⟨0, 1⟩ : IOCoins (ZMod 97)) 1 1) concreteOrbit4.βcoset
      ∧ ChipAgreement [(0 : Fin 1 → ZMod 97)] (⟨0, 1⟩ : IOCoins (ZMod 97)) 1
          (chipParams concreteOrbit4 (⟨0, 1⟩ : IOCoins (ZMod 97)) 1 1) concreteOrbit4.βcoset Pm
      ∧ ([(0 : Fin 1 → ZMod 97)]).length ≤ 3
      ∧ (∀ i, i < 3 → ∀ c : Fin 1,
          (rowEnv (chipParams concreteOrbit4 (⟨0, 1⟩ : IOCoins (ZMod 97)) 1 3)
            concreteOrbit4.βcoset Pp i).trace (4 + (c : ℕ))
              = listCol [(0 : Fin 1 → ZMod 97)] i c)
      ∧ (∀ i, i < 3 →
          ((rowEnv (chipParams concreteOrbit4 (⟨0, 1⟩ : IOCoins (ZMod 97)) 1 3)
            concreteOrbit4.βcoset Pp i).trace 2 = 1
              ↔ i < ([(0 : Fin 1 → ZMod 97)]).length)) := by
  have hcapP : (3 : ℕ) + 1 ≤ 2 ^ concreteOrbit4.h := by rw [concreteOrbit4_h]; norm_num
  have hcapM : ([(0 : Fin 1 → ZMod 97)]).length + 1 ≤ 2 ^ concreteOrbit4.h := by
    rw [concreteOrbit4_h]; norm_num
  obtain ⟨hsatP, _⟩ :=
    gatedChip_satisfies concreteOrbit4 (⟨0, 1⟩ : IOCoins (ZMod 97)) 1 3
      padAcc padInv padSel (fun _ => 1) (listCol [(0 : Fin 1 → ZMod 97)]) hcapP padGate
  obtain ⟨_, hsatM, hrowsM, hagM⟩ :=
    chip_satisfies concreteOrbit4 (⟨0, 1⟩ : IOCoins (ZMod 97)) 1
      [(0 : Fin 1 → ZMod 97)] padAcc padInv (fun _ => 1) (fun _ => 1) hcapM
      (by norm_num [padAcc])
      (by intro i hi; rw [listCol_rec1, compress_zero_rec]; norm_num [padInv])
      (by intro i _; norm_num)
      (by intro i _; norm_num)
      (by intro i hi
          have hi1 : i < 1 := by simpa using hi
          interval_cases i
          norm_num [padAcc, padInv])
      (by intro i hi
          have hi1 : i < 1 := by simpa using hi
          interval_cases i
          norm_num [padAcc, padInv])
      (by norm_num [padAcc])
  refine ⟨chipTrace concreteOrbit4 3 padAcc padInv padSel (fun _ => 1)
            (listCol [(0 : Fin 1 → ZMod 97)]),
          chipTrace concreteOrbit4 1 padAcc padInv (fun _ => 1) (fun _ => 1)
            (listCol [(0 : Fin 1 → ZMod 97)]),
          hcapP, hsatP, hsatM, hrowsM, hagM, by norm_num, ?_, ?_⟩
  · intro i hi c
    exact chipTrace_rec concreteOrbit4 (⟨0, 1⟩ : IOCoins (ZMod 97)) 1
      padAcc padInv padSel (fun _ => 1) (listCol [(0 : Fin 1 → ZMod 97)]) hcapP i (by omega) c
  · intro i hi
    have hread := chipTrace_mult concreteOrbit4 (⟨0, 1⟩ : IOCoins (ZMod 97)) 1
      padAcc padInv padSel (fun _ => 1) (listCol [(0 : Fin 1 → ZMod 97)]) hcapP i (by omega)
    constructor
    · intro h
      by_contra hcon
      have hin : ¬ i < 1 := by simpa using hcon
      have h0 : padSel i = 0 := by simp [padSel, hin]
      have hz : (0 : ZMod 97) = 1 := by rw [← h0]; exact hread.symm.trans h
      exact zero_ne_one hz
    · intro h
      have hin : i < 1 := by simpa using h
      have h1 : padSel i = 1 := by simp [padSel, hin]
      exact hread.trans h1

end ConcreteSound

end Nock.NockVMROM.Thm54.GatedIO

#print axioms Nock.NockVMROM.Thm54.GatedIO.ioSelAccStep_eq_ioMemAccStep
#print axioms Nock.NockVMROM.Thm54.GatedIO.finiteIOProgAIR_ignores_selector_slots
#print axioms Nock.NockVMROM.Thm54.GatedIO.ioInvPinGated_sound
#print axioms Nock.NockVMROM.Thm54.GatedIO.gated_padding_row_legal
#print axioms Nock.NockVMROM.Thm54.GatedIO.gated_eq_ungated_at_sel_one
#print axioms Nock.NockVMROM.Thm54.GatedIO.onehot_sum_eq
#print axioms Nock.NockVMROM.Thm54.GatedIO.GatedIOAccepts.terminal_eq_selected_sum
#print axioms Nock.NockVMROM.Thm54.GatedIO.GatedIOAccepts.ungated_of_selected_prefix
#print axioms Nock.NockVMROM.Thm54.GatedIO.gated_terminal_not_determined_by_records
#print axioms Nock.NockVMROM.Thm54.GatedIO.gatedChip_satisfies
#print axioms Nock.NockVMROM.Thm54.GatedIO.padded_gated_satisfies
#print axioms Nock.NockVMROM.Thm54.GatedIO.ungated_row_moves
#print axioms Nock.NockVMROM.Thm54.GatedIO.ungated_no_inert_row
#print axioms Nock.NockVMROM.Thm54.GatedIO.gated_padding_concrete
#print axioms Nock.NockVMROM.Thm54.GatedIO.gated_padded_domain_eq_computeDomain
#print axioms Nock.NockVMROM.Thm54.GatedIO.compRows_le_requests_length
#print axioms Nock.NockVMROM.Thm54.GatedIO.requests_row_count_ne
#print axioms Nock.NockVMROM.Thm54.GatedIO.padding_does_not_fit
#print axioms Nock.NockVMROM.Thm54.GatedIO.gated_accepts_of_satisfies
#print axioms Nock.NockVMROM.Thm54.GatedIO.gated_projWitness_accepts
#print axioms Nock.NockVMROM.Thm54.GatedIO.gated_io_lio_of_satisfies
#print axioms Nock.NockVMROM.Thm54.GatedIO.gated_sound_hypotheses_inhabited
