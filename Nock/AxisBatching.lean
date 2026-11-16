/-
  Nock/AxisBatching.lean

  The base `z^i` **axis-consistency batching soundness** — the paper's "all axis lookups
  valid" guarantee, which the paper SKETCHED and explicitly OMITTED.

  ⚠️ SCOPE (spec-redteam): this is proven about a STANDALONE idealized model `MTree` (below),
  NOT yet about the reified table.  `MTree`'s `indP`/`countsP`/`vaxis`/`Relaxis` faithfully
  MIRROR the `MemoryTable.eqBlk` axis recurrences (verified equivalent, `constr_counts_*`), but
  there is currently NO code-level bridge tying an `eqBlk`/`RAPmem`/`Vmem`/`memoryAIR`-satisfying
  memory-table trace to an `MTree`.  So this is a PARALLEL result — it proves the batch argument
  on the right recurrence, but does NOT yet DISCHARGE the real memory table's axis-lookup
  obligation.  Two things the idealization bakes in that the real table must supply: (a) the
  `K[X]` domain lift with monomial timestamps `X^e` (real `mem.ts : K`; "ts = z^i unique" is a
  cross-table compute obligation), (b) the trace-row-list → tree assembly.  Closing it needs a
  reification bridge lemma (`eqBlk`/`Vmem`-satisfying row list, chained BFS, `mem.ts = z^i` →
  an `MTree` with `(countsP t).eval z = root counts`, etc.), after which `axis_batching_sound_card`
  transfers.  That bridge = the follow-up sprint.  Also: SINGLE-ROOT only (base table); the
  multi-root `Corr:forest` extension is not instantiated here.  Until the bridge lands, this does
  NOT by itself "close the M1 axis-lookup gap".

  `read` carries `(T, C')`; `verify` still carries the committed axis for `vaxis`.

  ──────────────────────────────────────────────────────────────────────────────────────────
  THE RESTRUCTURED ARGUMENT (fixes a circularity in the naive "unconditional closed form").
  The naive `counts(v) = Σ relaxis·z^ts` is FALSE for a cheating prover: the `verify_child`
  gate injects an adversary-controlled `mem.axis`.  We split it:

  1. **`A_ind` — indicator closed form, UNCONDITIONAL** (`indP_coeff`).  The `axis_indicator`
     recurrence has NO adversarial coefficient; its `X^k`-coefficient is exactly
     `#{verify with ts=z^k} − #{read with ts=z^k}` — the multiset of active timestamps.

  2. **`A_cnt` — counts telescope with a per-record adversarial coefficient.**  We work with
     `axis_indicator`/`axis_counts` as POLYNOMIALS in `K[X]`.
     The doubling propagation is telescoped (`ccoef_spec`, the `acc_telescope`-analogue): the
     `X^k`-coefficient of `counts` is a scale-threaded fold `ccoef`.  Its closed form at the
     terminal boundary (`ccoef_full`) is, per record `r` with unique timestamp `X^{e_r}`,
        `(countsP root).coeff e_r = (mem.axis_r − relaxis_r) · (2⁻¹)^{depth_r}`
     — the **discrepancy identity** with the TRUE per-term scalar `(1/2)^{depth_r}` (`coeff_eq`),
     nonzero over `char ≠ 2`.

  3. **Distinctness is LOAD-BEARING** and enters as an EXPLICIT hypothesis: `readCount e t = 1`
     ∧ `verifyCount e t = 1` — the record is used, and its timestamp is UNIQUE.  If two records
     shared a timestamp, compensating errors `(+d, −d)` cancel and the check passes with BOTH
     axes wrong; then `.coeff e_r` sums two records and the factorization below breaks.  The
     discharge of distinctness from the compute-table line-number uniqueness is a SEPARATE
     cross-table step (flagged, NOT proven here).

  From the discrepancy identity + boundary `countsP root = 0` + the nonzero scalar we conclude
  `mem.axis_r = relaxis_r` (perfect, `axis_batching_sound`), and the Schwartz–Zippel form
  (`axis_batching_sound_card`, reusing `Walk.card_roots_le`): a cheating table with a wrong
  axis but boundary `eval z = 0` passes for at most `deg` of the challenges `z`.

  Position-free (§0): every quantity is a value/coefficient over the reconstructed tree — NO
  pointers, NO positional lookups.  Generic over an arbitrary field `K`; `goldilocks_prime` is
  NOT used (`char ≠ 2` is carried as the hypothesis `(2:K) ≠ 0`, the TRUE coefficient).
  ──────────────────────────────────────────────────────────────────────────────────────────
-/
import Nock.MemoryTable
import Nock.Walk

namespace Nock
namespace AxisBatching

open Polynomial

variable {K : Type*} [Field K]

/-! ## The reconstructed memory-walk tree

  A node of the memory BFS walk is one of the four `MState`s.  The child
  labels of `decompose` are its two subtrees; `read_root`/`verify_child` have a single child.  Each `read`/`verify` node references a memory record via the
  natural-number exponent `e` of its UNIQUE timestamp `z^e`.  `verify` additionally carries the ADVERSARIAL
  committed `axis` (`mem.axis`).  `halt` is a leaf.  Position-free: the tree is a value, not an indexed row set. -/
inductive MTree (K : Type*) where
  | halt : MTree K
  | decompose : MTree K → MTree K → MTree K
  | read : ℕ → MTree K → MTree K
  | verify : ℕ → K → MTree K → MTree K

namespace MTree

/-- Number of `read_root` nodes whose timestamp exponent is `e`. -/
def readCount (e : ℕ) : MTree K → ℕ
  | .halt => 0
  | .decompose l r => readCount e l + readCount e r
  | .read e' c => (if e' = e then 1 else 0) + readCount e c
  | .verify _ _ c => readCount e c

/-- Number of `verify_child` nodes whose timestamp exponent is `e`. -/
def verifyCount (e : ℕ) : MTree K → ℕ
  | .halt => 0
  | .decompose l r => verifyCount e l + verifyCount e r
  | .read _ c => verifyCount e c
  | .verify e' _ c => (if e' = e then 1 else 0) + verifyCount e c

omit [Field K] in
@[simp] theorem readCount_halt (e : ℕ) : readCount e (.halt : MTree K) = 0 := rfl
omit [Field K] in
@[simp] theorem verifyCount_halt (e : ℕ) : verifyCount e (.halt : MTree K) = 0 := rfl

/-! ## The `pw` / `counts` polynomials — form R (`MemoryTable.eqBlk`)

  Polynomials in `X = z` (timestamps `X^e`).  The accounting base `λ` and the per-exponent
  maps `T`/`C'` (keyed by timestamp exponent; `MTree.read` arity is unchanged) are
  parameters.  Goldilocks scale `λ^{pwScaleExp}` with `pwScaleExp = 63`.  Defaults
  `λ = 1`, `T = C' = 1` recover the unscaled indicator `± X^e`; they do **not** recover
  the paper's 2-adic doubling — that lives in `countsP_bin`. -/

/-- Form R scale `λ^{n−1}` (`n = 64` at Goldilocks). -/
noncomputable def pwScale (lmb : K) : K := lmb ^ (MemoryTable.pwScaleExp K)

@[simp] theorem pwScale_one : pwScale (1 : K) = 1 := one_pow _

/-- Form R `pw` (`Cell.indicator`). -/
noncomputable def indP (t : MTree K) (lmb : K := 1) (T : ℕ → K := fun _ => 1) : K[X] :=
  match t with
  | .halt => 0
  | .decompose l r => C lmb * (indP l lmb T + indP r lmb T)
  | .read e c => indP c lmb T - C (T e * pwScale lmb) * X ^ e
  | .verify e _ c => indP c lmb T + C (pwScale lmb) * X ^ e

/-- Form R `counts`. -/
noncomputable def countsP (t : MTree K) (lmb : K := 1) (T : ℕ → K := fun _ => 1)
    (C' : ℕ → K := fun _ => 1) : K[X] :=
  match t with
  | .halt => 0
  | .decompose l r =>
      countsP l lmb T C' + countsP r lmb T C'
        + C (lmb - 1) * (indP l lmb T + indP r lmb T) + indP r lmb T
  | .read e c => countsP c lmb T C' - C (T e * C' e) * X ^ e
  | .verify e _ c => countsP c lmb T C' + C (pwScale lmb) * X ^ e

/-- Substrate of Relaxis
    recovery; ignores form R's `T`/`C'`/`λ`. -/
noncomputable def indP_bin : MTree K → K[X]
  | .halt => 0
  | .decompose l r => indP_bin l + indP_bin r
  | .read e c => indP_bin c - X ^ e
  | .verify e _ c => indP_bin c + X ^ e

/-- Substrate of
    `axis_batching_sound` / Relaxis recovery; **not** `MemoryTable.eqBlk` after form R. -/
noncomputable def countsP_bin : MTree K → K[X]
  | .halt => 0
  | .decompose l r => C ((2 : K)⁻¹) * (countsP_bin l + countsP_bin r - indP_bin r)
  | .read e c => countsP_bin c - X ^ e
  | .verify e a c => countsP_bin c + C a * X ^ e

/-! ### Faithfulness: form R `indP`/`countsP` satisfy `MemoryTable.eqBlk` -/

theorem constr_ind_decompose (lmb : K) (T : ℕ → K) (l r : MTree K) :
    indP (.decompose l r) lmb T = C lmb * (indP l lmb T + indP r lmb T) := rfl
theorem constr_ind_read (lmb : K) (T : ℕ → K) (e : ℕ) (c : MTree K) :
    indP (.read e c) lmb T = indP c lmb T - C (T e * pwScale lmb) * X ^ e := rfl
theorem constr_ind_verify (lmb : K) (T : ℕ → K) (e : ℕ) (a : K) (c : MTree K) :
    indP (.verify e a c) lmb T = indP c lmb T + C (pwScale lmb) * X ^ e := rfl
theorem constr_ind_halt (lmb : K) (T : ℕ → K) : indP (.halt : MTree K) lmb T = 0 := rfl

theorem constr_counts_decompose (lmb : K) (T C' : ℕ → K) (l r : MTree K) :
    countsP (.decompose l r) lmb T C' =
      countsP l lmb T C' + countsP r lmb T C'
        + C (lmb - 1) * (indP l lmb T + indP r lmb T) + indP r lmb T := rfl
theorem constr_counts_read (lmb : K) (T C' : ℕ → K) (e : ℕ) (c : MTree K) :
    countsP (.read e c) lmb T C' = countsP c lmb T C' - C (T e * C' e) * X ^ e := rfl
theorem constr_counts_verify (lmb : K) (T C' : ℕ → K) (e : ℕ) (a : K) (c : MTree K) :
    countsP (.verify e a c) lmb T C' = countsP c lmb T C' + C (pwScale lmb) * X ^ e := rfl
theorem constr_counts_halt (lmb : K) (T C' : ℕ → K) : countsP (.halt : MTree K) lmb T C' = 0 := rfl

/-- Default `λ = 1`, `T = 1` recovers the unscaled indicator (paper `± ts`). -/
theorem indP_default_read (e : ℕ) (c : MTree K) :
    indP (.read e c) = indP c - X ^ e := by
    simp [indP, pwScale, one_pow, one_mul]

theorem indP_default_verify (e : ℕ) (a : K) (c : MTree K) :
    indP (.verify e a c) = indP c + X ^ e := by
  simp [indP, pwScale, one_pow, one_mul]

theorem indP_default_decompose (l r : MTree K) :
    indP (.decompose l r) = indP l + indP r := by
  simp [indP]

/-- Default `λ = 1`, `T = C' = 1` recovers unscaled `counts` (paper `± ts`)
    plus the form-R decompose remainder `+ indP r`. -/
theorem countsP_default_read (e : ℕ) (c : MTree K) :
    countsP (.read e c) = countsP c - X ^ e := by
  simp [countsP]

theorem countsP_default_verify (e : ℕ) (a : K) (c : MTree K) :
    countsP (.verify e a c) = countsP c + X ^ e := by
  simp [countsP, pwScale, one_pow, one_mul]

theorem countsP_default_decompose (l r : MTree K) :
    countsP (.decompose l r) = countsP l + countsP r + indP r := by
  simp [countsP]


theorem constr_counts_bin_decompose (h2 : (2 : K) ≠ 0) (l r : MTree K) :
    2 * countsP_bin (.decompose l r) = countsP_bin l + countsP_bin r - indP_bin r := by
  have h2poly : (2 : K[X]) = C (2 : K) := (map_ofNat C 2).symm
  have hmul : (2 : K[X]) * C ((2 : K)⁻¹) = 1 := by
    rw [h2poly, ← C_mul, mul_inv_cancel₀ h2, C_1]
  show (2 : K[X]) * (C ((2 : K)⁻¹) * (countsP_bin l + countsP_bin r - indP_bin r)) = _
  rw [← mul_assoc, hmul, one_mul]

theorem constr_counts_bin_read (e : ℕ) (c : MTree K) :
    countsP_bin (.read e c) = countsP_bin c - X ^ e := rfl
theorem constr_counts_bin_verify (e : ℕ) (a : K) (c : MTree K) :
    countsP_bin (.verify e a c) = countsP_bin c + C a * X ^ e := rfl
theorem constr_counts_bin_halt : countsP_bin (.halt : MTree K) = 0 := rfl

/-! ## `A_ind` — the indicator closed form

  The `X^k`-coefficient of `axis_indicator` at any node is exactly the (signed) multiset of
  active timestamps in its subtree: `#{verify_child with ts=z^k} − #{read_root with ts=z^k}`.
  There is NO adversarial coefficient — this is the "sum of `z^{i_j}`" of the paper. -/
theorem indP_coeff (t : MTree K) (k : ℕ) :
    (indP_bin t).coeff k = (verifyCount k t : K) - (readCount k t : K) := by
  induction t with
  | halt => simp [indP_bin, verifyCount, readCount]
  | decompose l r ihl ihr =>
      simp only [indP_bin, verifyCount, readCount, coeff_add, ihl, ihr]
      push_cast; ring
  | read e c ih =>
      simp only [indP_bin, verifyCount, readCount, coeff_sub, coeff_X_pow, ih]
      by_cases h : e = k
      · subst h; simp; ring
      · rw [if_neg (fun hh => h hh.symm), if_neg h]; push_cast; ring
  | verify e a c ih =>
      simp only [indP_bin, verifyCount, readCount, coeff_add, coeff_X_pow, ih]
      by_cases h : e = k
      · subst h; simp; ring
      · rw [if_neg (fun hh => h hh.symm), if_neg h]; push_cast; ring

/-! ## `A_cnt` — the counts telescope

  `ccoef s e t` is the scale-`s`-threaded fold computing `s · (countsP_bin t).coeff e`.  The
  doubling of `decompose` is carried by halving the scale `s ↦ s/2` into each child, with the `−ind_rc` term entering through the
  `axis_indicator` coefficient `(indP_bin r).coeff e`. -/
noncomputable def ccoef (s : K) (e : ℕ) : MTree K → K
  | .halt => 0
  | .decompose l r =>
      ccoef (s * (2 : K)⁻¹) e l + ccoef (s * (2 : K)⁻¹) e r
        - (s * (2 : K)⁻¹) * (indP_bin r).coeff e
  | .read e' c => ccoef s e c - (if e' = e then s else 0)
  | .verify e' a c => ccoef s e c + (if e' = e then s * a else 0)

/-- **`ccoef` computes the scaled counts coefficient** (the telescoping identity, unconditional). -/
theorem ccoef_spec (e : ℕ) (t : MTree K) :
    ∀ s : K, s * (countsP_bin t).coeff e = ccoef s e t := by
  induction t with
  | halt => intro s; simp [countsP_bin, ccoef]
  | decompose l r ihl ihr =>
      intro s
      rw [countsP_bin, ccoef, ← ihl (s * (2 : K)⁻¹), ← ihr (s * (2 : K)⁻¹)]
      simp only [coeff_C_mul, coeff_add, coeff_sub]; ring
  | read e' c ih =>
      intro s
      rw [countsP_bin, ccoef, ← ih s]
      simp only [coeff_sub, coeff_X_pow]
      by_cases h : e' = e
      · subst h; simp; ring
      · rw [if_neg (fun hh => h hh.symm), if_neg h]; ring
  | verify e' a c ih =>
      intro s
      rw [countsP_bin, ccoef, ← ih s]
      simp only [coeff_add, coeff_C_mul, coeff_X_pow]
      by_cases h : e' = e
      · subst h; simp; ring
      · rw [if_neg (fun hh => h hh.symm), if_neg h]; ring

/-- **`ccoef` vanishes when timestamp `e` is ABSENT** (no `read`/`verify` node uses it). -/
theorem ccoef_absent (e : ℕ) (t : MTree K) :
    ∀ s : K, readCount e t = 0 → verifyCount e t = 0 → ccoef s e t = 0 := by
  induction t with
  | halt => intro s _ _; simp [ccoef]
  | decompose l r ihl ihr =>
      intro s hr hv
      simp only [readCount] at hr; simp only [verifyCount] at hv
      have hrl : readCount e l = 0 := by omega
      have hrr : readCount e r = 0 := by omega
      have hvl : verifyCount e l = 0 := by omega
      have hvr : verifyCount e r = 0 := by omega
      rw [ccoef, ihl _ hrl hvl, ihr _ hrr hvr, indP_coeff, hvr, hrr]
      simp
  | read e' c ih =>
      intro s hr hv
      simp only [readCount] at hr; simp only [verifyCount] at hv
      have he : e' ≠ e := by rintro rfl; simp at hr
      rw [ccoef, if_neg he, ih _ (by omega) hv]; ring
  | verify e' a c ih =>
      intro s hr hv
      simp only [readCount] at hr; simp only [verifyCount] at hv
      have he : e' ≠ e := by rintro rfl; simp at hv
      rw [ccoef, if_neg he, ih _ hr (by omega)]; ring

/-! ### The topological "true axis" `relaxis` and the record depth (DERIVED by the doubling)

  `vdep e t` = number of `decompose` nodes on the path to the `verify_child` node with
  timestamp `e` (its depth), `vaxis e t` = its COMMITTED `mem.axis`, `vaddr e t` = the binary
  address accumulated from the region root down to it (`⟶left` doubles, `⟶right` doubles+`1`).
  `Relaxis e t` = the address of the `verify_child` RELATIVE to its `read_root` = the leading-`1`
  binary address `vaddr + 2^{vdep}` = `axis_root(child)`, PINNED by the walk topology (L1). -/

/-- Depth (number of `decompose` ancestors) of the `verify_child` node with timestamp `e`. -/
def vdep (e : ℕ) : MTree K → ℕ
  | .halt => 0
  | .decompose l r => (if verifyCount e l = 1 then vdep e l else vdep e r) + 1
  | .read _ c => vdep e c
  | .verify e' _ c => if e' = e then 0 else vdep e c

/-- The COMMITTED axis `mem.axis` of the `verify_child` node with timestamp `e` (adversarial). -/
noncomputable def vaxis (e : ℕ) : MTree K → K
  | .halt => 0
  | .decompose l r => if verifyCount e l = 1 then vaxis e l else vaxis e r
  | .read _ c => vaxis e c
  | .verify e' a c => if e' = e then a else vaxis e c

/-- The binary address accumulated by the decompose-path doubling, from the current subtree's
    root down to the `verify_child` with timestamp `e`. -/
noncomputable def vaddr (e : ℕ) : MTree K → K
  | .halt => 0
  | .decompose l r => if verifyCount e l = 1 then vaddr e l else vaddr e r + (2 : K) ^ (vdep e r)
  | .read _ c => vaddr e c
  | .verify e' _ c => if e' = e then 0 else vaddr e c

/-- The **topological true axis** `relaxis = axis_root(child)`: the leading-`1` binary address of
    the `verify_child` relative to its `read_root`.  DERIVED by the doubling. -/
noncomputable def Relaxis (e : ℕ) : MTree K → K
  | .halt => 0
  | .decompose l r => if readCount e l = 1 then Relaxis e l else Relaxis e r
  | .read e' c => if e' = e then vaddr e c + (2 : K) ^ (vdep e c) else Relaxis e c
  | .verify _ _ c => Relaxis e c

/-! ### `ccoef_pending` — the doubling closed form BELOW the `read_root` (the pending region)

  Where timestamp `e` is pending (its `read_root` already passed above, `readCount e t = 0`,
  and its `verify_child` still ahead, `verifyCount e t = 1`), the counts coefficient is
  `s·(mem.axis − vaddr)·(1/2)^{vdep}` — the doubling reconstructs the address `vaddr` and the
  committed `mem.axis` is removed at the `verify_child`. -/
theorem ccoef_pending (h2 : (2 : K) ≠ 0) (e : ℕ) (t : MTree K) :
    ∀ s : K, readCount e t = 0 → verifyCount e t = 1 →
      ccoef s e t = s * (vaxis e t - vaddr e t) * ((2 : K)⁻¹) ^ (vdep e t) := by
  induction t with
  | halt => intro s _ hv; simp [verifyCount] at hv
  | decompose l r ihl ihr =>
      intro s hr hv
      simp only [readCount] at hr; simp only [verifyCount] at hv
      have hrl : readCount e l = 0 := by omega
      have hrr : readCount e r = 0 := by omega
      by_cases hvl : verifyCount e l = 1
      · -- verify in LEFT
        have hvr : verifyCount e r = 0 := by omega
        rw [ccoef, ihl _ hrl hvl, ccoef_absent e r _ hrr hvr, indP_coeff, hvr, hrr]
        simp only [vaxis, vaddr, vdep, if_pos hvl]
        rw [pow_succ]; push_cast; ring
      · -- verify in RIGHT
        have hvr : verifyCount e r = 1 := by omega
        rw [ccoef, ccoef_absent e l _ hrl (by omega), ihr _ hrr hvr, indP_coeff, hvr, hrr]
        simp only [vaxis, vaddr, vdep, if_neg hvl]
        rw [pow_succ]
        have hpow : (2 : K) ^ (vdep e r) * ((2 : K)⁻¹) ^ (vdep e r) = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ h2, one_pow]
        push_cast
        -- goal: (s*2⁻¹)*(vaxis r - vaddr r)*(2⁻¹)^{vdep r} - (s*2⁻¹)*(1-0)
        --       = s*(vaxis r - (vaddr r + 2^{vdep r}))*((2⁻¹)^{vdep r}*2⁻¹)
        linear_combination (s * (2:K)⁻¹) * hpow
  | read e' c ih =>
      intro s hr hv
      simp only [readCount] at hr; simp only [verifyCount] at hv
      have he : e' ≠ e := by rintro rfl; simp at hr
      rw [ccoef, if_neg he, ih _ (by omega) hv]
      simp only [vaxis, vaddr, vdep, sub_zero]
  | verify e' a c ih =>
      intro s hr hv
      simp only [readCount] at hr; simp only [verifyCount] at hv
      by_cases he : e' = e
      · have hvc : verifyCount e c = 0 := by rw [if_pos he] at hv; omega
        rw [ccoef, if_pos he, ccoef_absent e c _ hr hvc]
        simp only [vaxis, vaddr, vdep, if_pos he]; simp
      · rw [ccoef, if_neg he, ih _ hr (by simpa [he] using hv)]
        simp only [vaxis, vaddr, vdep, if_neg he, add_zero]

/-! ### `Nested` — the reconstructed-tree well-nesting (`read_root` ancestor of `verify_child`)

  In a genuine BFS walk a record's `read_root` is an ancestor of its `verify_child`.  `Nested e t` captures this for timestamp `e`: at
  each `decompose` the read-side is the verify-side (no crossing), and no `read_root` for `e`
  sits BELOW its `verify_child`.  This is a structural property of the reconstructed tree
  (the memory-side analogue of `Walk.BFSValid`); its discharge is the tree-reconstruction step. -/
def Nested (e : ℕ) : MTree K → Prop
  | .halt => True
  | .decompose l r =>
      (readCount e l = 1 → verifyCount e l = 1) ∧ (readCount e r = 1 → verifyCount e r = 1)
        ∧ Nested e l ∧ Nested e r
  | .read _ c => Nested e c
  | .verify e' _ c => (e' = e → readCount e c = 0) ∧ Nested e c

/-! ### `ccoef_full` — the full discrepancy closed form (the record is USED: read AND verified)

  With the `read_root` present (`readCount e t = 1`) and the `verify_child` present
  (`verifyCount e t = 1`) and the tree well-nested, the counts coefficient factors as
  `s·(mem.axis − relaxis)·(1/2)^{vdep}` where `relaxis = Relaxis` is the TRUE topological axis. -/
theorem ccoef_full (h2 : (2 : K) ≠ 0) (e : ℕ) (t : MTree K) :
    ∀ s : K, Nested e t → readCount e t = 1 → verifyCount e t = 1 →
      ccoef s e t = s * (vaxis e t - Relaxis e t) * ((2 : K)⁻¹) ^ (vdep e t) := by
  induction t with
  | halt => intro s _ hr _; simp [readCount] at hr
  | decompose l r ihl ihr =>
      intro s hn hr hv
      simp only [readCount] at hr; simp only [verifyCount] at hv
      obtain ⟨hnl, hnr, hNl, hNr⟩ := hn
      by_cases hrl : readCount e l = 1
      · -- read (and hence verify) in LEFT
        have hvl : verifyCount e l = 1 := hnl hrl
        have hrr : readCount e r = 0 := by omega
        have hvr : verifyCount e r = 0 := by omega
        rw [ccoef, ihl _ hNl hrl hvl, ccoef_absent e r _ hrr hvr, indP_coeff, hvr, hrr]
        simp only [vaxis, Relaxis, vdep, if_pos hvl, if_pos hrl]
        rw [pow_succ]; push_cast; ring
      · -- read (and hence verify) in RIGHT
        have hrr : readCount e r = 1 := by omega
        have hvr : verifyCount e r = 1 := hnr hrr
        have hvl : verifyCount e l = 0 := by omega
        have hrl0 : readCount e l = 0 := by omega
        rw [ccoef, ccoef_absent e l _ hrl0 hvl, ihr _ hNr hrr hvr, indP_coeff, hvr, hrr]
        have hvlne : ¬ verifyCount e l = 1 := by omega
        have hrlne : ¬ readCount e l = 1 := by omega
        simp only [vaxis, Relaxis, vdep, if_neg hvlne, if_neg hrlne]
        rw [pow_succ]; push_cast; ring
  | read e' c ih =>
      intro s hn hr hv
      simp only [readCount] at hr; simp only [verifyCount] at hv
      by_cases he : e' = e
      · -- this is the record's read_root: below is the pending region
        have hrc : readCount e c = 0 := by rw [if_pos he] at hr; omega
        rw [ccoef, if_pos he, ccoef_pending h2 e c _ hrc hv]
        simp only [vaxis, Relaxis, vdep, if_pos he]
        have hpow : (2 : K) ^ (vdep e c) * ((2 : K)⁻¹) ^ (vdep e c) = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ h2, one_pow]
        -- goal: s*(vaxis c - vaddr c)*(2⁻¹)^{vdep c} - s = s*(vaxis c - (vaddr c + 2^{vdep c}))*(2⁻¹)^{vdep c}
        linear_combination s * hpow
      · rw [ccoef, if_neg he, ih _ hn (by simpa [he] using hr) hv]
        simp only [vaxis, Relaxis, vdep, if_neg he, sub_zero]
  | verify e' a c ih =>
      intro s hn hr hv
      simp only [readCount] at hr; simp only [verifyCount] at hv
      obtain ⟨hnv, hNc⟩ := hn
      by_cases he : e' = e
      · -- verify_child ABOVE its read_root — excluded by well-nesting
        have := hnv he
        omega
      · have hvc : verifyCount e c = 1 := by simpa [he] using hv
        rw [ccoef, if_neg he, ih _ hNc hr hvc]
        simp only [vaxis, Relaxis, vdep, if_neg he, add_zero]

/-! ## The discrepancy identity and the axis-batching soundness theorems -/

/-- **The discrepancy identity**.  For a USED record
    with UNIQUE timestamp `e` (`readCount e t = 1 ∧ verifyCount e t = 1` — the distinctness
    hypothesis), the `X^e`-coefficient of `axis_counts` at the root is
      `(countsP_bin t).coeff e = (mem.axis − relaxis) · (2⁻¹)^{depth}`,
    with `mem.axis = vaxis e t` (committed), `relaxis = Relaxis e t` (true topological axis),
    and the TRUE per-term scalar `(2⁻¹)^{depth}`, nonzero over `char ≠ 2`. -/
theorem coeff_eq (h2 : (2 : K) ≠ 0) (e : ℕ) (t : MTree K)
    (hn : Nested e t) (hr : readCount e t = 1) (hv : verifyCount e t = 1) :
    (countsP_bin t).coeff e = (vaxis e t - Relaxis e t) * ((2 : K)⁻¹) ^ (vdep e t) := by
  have h := ccoef_spec e t 1
  rw [ccoef_full h2 e t 1 hn hr hv] at h
  simpa using h

/-- The per-term scalar `(2⁻¹)^{depth}` is nonzero over `char ≠ 2`. -/
theorem scalar_ne_zero (h2 : (2 : K) ≠ 0) (d : ℕ) : ((2 : K)⁻¹) ^ d ≠ 0 :=
  pow_ne_zero _ (inv_ne_zero h2)

/-- **Base axis-batching soundness (PERFECT form).**  Given the reconstructed memory-walk tree
    `t`, `char ≠ 2`, and the terminal boundary `countsP_bin t = 0`, EVERY used memory record — identified by its unique timestamp exponent `e`
    with `readCount e t = 1` (used) ∧ `verifyCount e t = 1` (verified, and DISTINCT) and a
    well-nested tree — has its committed axis equal to the true axis:
      `mem.axis_e (= vaxis e t) = axis_root(child_e) (= Relaxis e t)`.
    This is the paper's "all axis lookups are valid" guarantee — proven
    here ON THE IDEALIZED `MTree`; discharging it for the reified table awaits the reification
    bridge (see the file-header SCOPE note). -/
theorem axis_batching_sound (h2 : (2 : K) ≠ 0) (t : MTree K) (hterm : countsP_bin t = 0)
    (e : ℕ) (hn : Nested e t) (hr : readCount e t = 1) (hv : verifyCount e t = 1) :
    vaxis e t = Relaxis e t := by
  have hc : (vaxis e t - Relaxis e t) * ((2 : K)⁻¹) ^ (vdep e t) = 0 := by
    rw [← coeff_eq h2 e t hn hr hv, hterm, coeff_zero]
  have := (mul_eq_zero.mp hc).resolve_right (scalar_ne_zero h2 (vdep e t))
  exact sub_eq_zero.mp this

/-- **Base axis-batching soundness.**  If some
    used record's committed axis is WRONG (`vaxis e t ≠ Relaxis e t`) but the terminal boundary
    is checked at a random challenge `z` (`(countsP_bin t).eval z = 0` — the polynomial column is
    "represented by its evaluation at a random extension field element", the paper), then at
    most `deg(axis_counts)` of the `|K|` challenges accept the cheating table.  Reuses
    `Walk.card_roots_le`; the probability is `≤ deg/|K|`, exactly the walk-soundness pattern. -/
theorem axis_batching_sound_card [Fintype K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (t : MTree K) (e : ℕ)
    (hn : Nested e t) (hr : readCount e t = 1) (hv : verifyCount e t = 1)
    (hbad : vaxis e t ≠ Relaxis e t) :
    (Finset.univ.filter (fun z : K => (countsP_bin t).eval z = 0)).card
      ≤ (countsP_bin t).natDegree := by
  have hcoeff : (countsP_bin t).coeff e ≠ 0 := by
    rw [coeff_eq h2 e t hn hr hv]
    exact mul_ne_zero (sub_ne_zero.mpr hbad) (scalar_ne_zero h2 (vdep e t))
  have hne : countsP_bin t ≠ 0 := fun h => hcoeff (by rw [h, coeff_zero])
  have hset : (Finset.univ.filter (fun z : K => (countsP_bin t).eval z = 0))
      = (Finset.univ.filter (fun z : K => (countsP_bin t).IsRoot z)) := rfl
  rw [hset]; exact Nock.Walk.card_roots_le _ hne

/-! ## Distinctness is LOAD-BEARING — a concrete attack when timestamps COLLIDE

  If two records share a timestamp `z^e` (distinctness violated, so `readCount e t = 2`), the
  `X^e`-coefficient of `axis_counts` is the SUM of both records' discrepancies, and compensating
  errors `(+d, −d)` cancel: the terminal boundary `countsP_bin t = 0` passes while BOTH committed
  axes are wrong.  Here both records are read-then-immediately-verified (no `decompose` between,
  so the true axis is `1`), but are committed axes `0` and `2` — both `≠ 1`, yet the check
  accepts.  This is exactly the attack the `readCount e t = 1 ∧ verifyCount e t = 1` hypothesis
  of `axis_batching_sound` rules out; its discharge (unique per-lookup timestamps) is the
  compute-table line-number-uniqueness cross-table obligation. -/
theorem distinctness_load_bearing (e : ℕ) :
    let t : MTree K :=
      .decompose (.read e (.verify e 0 .halt)) (.read e (.verify e 2 .halt))
    countsP_bin t = 0 ∧ readCount e t = 2 ∧ verifyCount e t = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · show countsP_bin
      (.decompose (.read e (.verify e (0:K) .halt)) (.read e (.verify e 2 .halt))) = 0
    simp only [countsP_bin, indP_bin, map_zero, zero_add, zero_mul, one_mul, map_one]
    rw [show (C (2:K)) = (2:K[X]) from map_ofNat C 2]
    ring
  · simp [readCount]
  · simp [verifyCount]

end MTree
end AxisBatching
end Nock
