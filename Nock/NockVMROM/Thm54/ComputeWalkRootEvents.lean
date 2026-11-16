/-
  Nock/NockVMROM/Thm54/ComputeWalkRootEvents.lean

  **H1.5a walk-α Move B — the compute walk's ROOT events, priced.**

  `Thm:Walk_IOP` recognizes `rvt_root` by seeding the walk with
  `(seed, initial_count) = (α · RLC^γ(rvt_root), α)` and checking `out_walk = 0`; its
  soundness error is `h/|𝕂|` (`:966`). The proof (`:2263-2302`) telescopes the accumulator to
  `acc_walk(k) = −node_list_k(α) + node_queue_k(α)` (`:2294`), where `node_queue` starts from
  `RLC^γ(current_node(1,·)) · X` (`:2270`) — and at `:2293` it **identifies** the public seed's
  root with the committed first row, `seed = RLC^γ(slt)·α = RLC^γ(current_node(1,·))·α`. On a
  hostile trace those are two different objects: the verifier's `RLC^γ(rvt_root)` (the claim,
  `:962`) and the prover's `current_node(1,·)`. What the walk gates actually give
  (`acc_closed_seeded` below, `acc_telescope` with the seed left free) is
  `acc_walk(h) = −node_list_h(α) + node_queue_h^{root}(α)` with the public root in the `X¹` term. So `out_walk = 0` says `α` is a root of the polynomial
  `rootDiffP := node_list_h(X) − node_queue_h^{root}(X)`, and *outside* its root set that
  polynomial is zero — whose `X¹` coefficient reads `current_node(1,·) = rvt_root`
  (`cur_one_eq_root_of_walkSat`).

  **Degree majorant.**  `deg ≤ max(h, 1 + Σ_{i≤h} fanout(j(i)))` (`nodeListP_natDegree_le`,
  `nodeQueueP_natDegree_le`; the paper's `:2276-2278` degree formula is an upper bound in the tree).
  The paper's `h/|𝕂|` presupposes the tiling `Σ fanout + 1 = h` (`Walk.walk_soundness_card`'s
  `hdeg`), which the deployed compute chip does not force.  With every compute fanout `≤ 3` (`fanoutComp_le_three`) the
  degree is `≤ 3h + 1`, so the priced summand is **`(3N + 1)/|𝕂|`** at `N = h` compute rows —
  `walkAlphaRootBound`.  A worse constant than the paper's `h`, disclosed.

-- the paper
-/
import Nock.Walk
import Nock.NockVMROM.Thm54.JointCoins
import Nock.NockVMROM.Thm54.ComputeWalkLabel
import Nock.NockVMROM.Thm54.ComputeEnvAgreement
import Nock.NockVMROM.Thm54.ExprSubstitution

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.ComputeWalkRootEvents

open scoped Classical
open Polynomial
open Nock
open Nock.Reified
open Nock.ComputeTable
open Nock.Walk
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution

noncomputable section

/-! ## 1. Trace-only expressions

A syntactic check that an `Expr` reads no challenge and no public slot.  Evaluation of such
an expression depends on the trace columns alone (`eval_congr_of_traceOnly`).  This is the
instrument behind "the decoded label is a function of the committed trace". -/

/-- `true` iff the expression mentions only `traceCur`/`traceNext` variables and constants. -/
def traceOnly : Expr → Bool
  | .Var .traceCur _ => true
  | .Var .traceNext _ => true
  | .Var .challenge _ => false
  | .Var .publicVal _ => false
  | .Const _ => true
  | .Add a b => traceOnly a && traceOnly b
  | .Sub a b => traceOnly a && traceOnly b
  | .Mul a b => traceOnly a && traceOnly b
  | .Neg a => traceOnly a
  | .Pow a _ => traceOnly a

section TraceOnly
variable {K : Type} [Field K]

/-- A trace-only expression evaluates identically in two environments with the same trace
columns. -/
theorem eval_congr_of_traceOnly :
    ∀ (e : Expr), traceOnly e = true → ∀ {E E' : Env K},
      E.trace = E'.trace → E.traceNext = E'.traceNext → e.eval E = e.eval E'
  | .Var .traceCur i, _, _, _, ht, _ => by simp only [Expr.eval, ht]
  | .Var .traceNext i, _, _, _, _, htn => by simp only [Expr.eval, htn]
  | .Var .challenge _, h, _, _, _, _ => by simp [traceOnly] at h
  | .Var .publicVal _, h, _, _, _, _ => by simp [traceOnly] at h
  | .Const _, _, _, _, _, _ => rfl
  | .Add a b, h, _, _, ht, htn => by
      have hab := Bool.and_eq_true_iff.mp h
      simp only [Expr.eval, eval_congr_of_traceOnly a hab.1 ht htn,
        eval_congr_of_traceOnly b hab.2 ht htn]
  | .Sub a b, h, _, _, ht, htn => by
      have hab := Bool.and_eq_true_iff.mp h
      simp only [Expr.eval, eval_congr_of_traceOnly a hab.1 ht htn,
        eval_congr_of_traceOnly b hab.2 ht htn]
  | .Mul a b, h, _, _, ht, htn => by
      have hab := Bool.and_eq_true_iff.mp h
      simp only [Expr.eval, eval_congr_of_traceOnly a hab.1 ht htn,
        eval_congr_of_traceOnly b hab.2 ht htn]
  | .Neg a, h, _, _, ht, htn => by
      simp only [Expr.eval, eval_congr_of_traceOnly a h ht htn]
  | .Pow a _, h, _, _, ht, htn => by
      simp only [Expr.eval, eval_congr_of_traceOnly a h ht htn]

end TraceOnly

/-- **Measured:** every restored fingerprint source `semanticPub .traceCur role coord`
(`role < 12`, `coord < 3`) reads trace columns only — the `restored*Field` bodies are
`pubFP`/`decFP`/selector/`Const` terms (`OptimizedComputeSubstitution.lean`).  Instrument:
`traceOnly` by `decide` over the 36 slots. -/
theorem traceOnly_semanticPub :
    ∀ role, role < 12 → ∀ coord, coord < 3 →
      traceOnly (semanticPub .traceCur role coord) = true := by
  decide

/-- The trace-only check on the hosted child-tag reads (`childTagHost curReader`). -/
theorem traceOnly_childTagHost (st : State) (j : Fin 3) :
    traceOnly (childTagHost curReader st j) = true := by
  cases st <;> fin_cases j <;> rfl

/-! ## 2. Row decoders (trace-only, package-free)

The same instruments `DeployedComputeRows.decodePub` / `StrategyOfTraces.computeStateOf` use,
restated upstream of the package so the consumed failure event can name them.  The state is
read off the one-hot selector columns `1..10` (column `0` shared by `s0`/`cons`, as in
`computeStateOf`: on an accepted row `OneHotSelector` makes the read exact). -/

section RowDecoders
variable {K : Type} [Field K]

/-- Selector-column state decoder (body identical to `StrategyOfTraces.computeStateOf`). -/
def rowStateOf (E : Env K) : State :=
  if E.trace 1 = 1 then .s1
  else if E.trace 2 = 1 then .s2
  else if E.trace 3 = 1 then .s3
  else if E.trace 4 = 1 then .s4
  else if E.trace 5 = 1 then .s5
  else if E.trace 6 = 1 then .s6
  else if E.trace 7 = 1 then .s7
  else if E.trace 8 = 1 then .s8
  else if E.trace 9 = 1 then .s9
  else if E.trace 10 = 1 then .cons
  else .s0

/-- The row's `Pub` decoded through the production substitution at the decoded state
(`DeployedComputeRows.decodePub` on a source environment). -/
def rowPub (E : Env K) : Pub K :=
  pubOfState (Env.ofSubst computeSubst E) (rowStateOf E)

/-- The row's `LT_comp` label vector. -/
def rowLabelVec (E : Env K) : Fin 10 → K := labelVecOfPub (rowPub E)

/-- The three hosted child state tags (Option A overlay hosts). -/
def rowTags (E : Env K) : Fin 3 → K :=
  fun j => (childTagHost curReader (rowStateOf E) j).eval E

/-- The declared child payload of slot `l` (0-indexed; out-of-range slots are `0`). -/
def rowChildVec (E : Env K) (l : ℕ) : Fin 10 → K :=
  childVecN (rowPub E) (rowTags E) l

/-- The decoded fanout. -/
def rowFanout (E : Env K) : ℕ := fanoutComp (rowStateOf E)

theorem rowFanout_le_three (E : Env K) : rowFanout E ≤ 3 :=
  fanoutComp_le_three _

theorem rowStateOf_congr {E E' : Env K} (h : E.trace = E'.trace) :
    rowStateOf E = rowStateOf E' := by
  unfold rowStateOf
  rw [h]

/-- The decoded fingerprint columns `11..46` read trace columns only. -/
theorem ofSubst_trace_congr {E E' : Env K} (ht : E.trace = E'.trace)
    (htn : E.traceNext = E'.traceNext) (k : ℕ) (hk : 11 ≤ k ∧ k < 47) :
    (Env.ofSubst computeSubst E).trace k = (Env.ofSubst computeSubst E').trace k := by
  have h11 : ¬ k < 11 := by omega
  have h47 : k < 47 := hk.2
  simp only [Env.ofSubst, computeSubst, computeTraceSubst, h11, h47, if_false, if_true]
  exact eval_congr_of_traceOnly _
    (traceOnly_semanticPub _ (by omega) _ (Nat.mod_lt _ (by norm_num))) ht htn

/-- A decoded fingerprint triple based at `b ∈ [11, 45)` reads trace columns only. -/
theorem fpOf_ofSubst_congr {E E' : Env K} (ht : E.trace = E'.trace)
    (htn : E.traceNext = E'.traceNext) (b : ℕ) (hb : 11 ≤ b ∧ b + 2 < 47) :
    fpOf (Env.ofSubst computeSubst E) b = fpOf (Env.ofSubst computeSubst E') b := by
  simp only [fpOf]
  rw [ofSubst_trace_congr ht htn b (by omega), ofSubst_trace_congr ht htn (b + 1) (by omega),
    ofSubst_trace_congr ht htn (b + 2) (by omega)]

theorem rowPub_s_congr {E E' : Env K} (ht : E.trace = E'.trace)
    (htn : E.traceNext = E'.traceNext) : (rowPub E).s = (rowPub E').s := by
  simp only [rowPub, pubOfState]
  exact fpOf_ofSubst_congr ht htn 11 (by omega)

theorem rowPub_f_congr {E E' : Env K} (ht : E.trace = E'.trace)
    (htn : E.traceNext = E'.traceNext) : (rowPub E).f = (rowPub E').f := by
  simp only [rowPub, pubOfState]
  exact fpOf_ofSubst_congr ht htn 14 (by omega)

theorem rowPub_e_congr {E E' : Env K} (ht : E.trace = E'.trace)
    (htn : E.traceNext = E'.traceNext) : (rowPub E).e = (rowPub E').e := by
  simp only [rowPub, pubOfState]
  exact fpOf_ofSubst_congr ht htn 17 (by omega)

theorem rowPub_state_congr {E E' : Env K} (ht : E.trace = E'.trace) :
    (rowPub E).state = (rowPub E').state := by
  simp only [rowPub, pubOfState]
  exact rowStateOf_congr ht

theorem rowPub_sfTriple_congr {E E' : Env K} (ht : E.trace = E'.trace)
    (htn : E.traceNext = E'.traceNext) (j : Fin 3) :
    sfTriple (rowPub E) j = sfTriple (rowPub E') j := by
  fin_cases j
  · simp only [sfTriple, rowPub, pubOfState]
    rw [fpOf_ofSubst_congr ht htn 20 (by omega), fpOf_ofSubst_congr ht htn 23 (by omega),
      fpOf_ofSubst_congr ht htn 26 (by omega)]
  · simp only [sfTriple, rowPub, pubOfState]
    rw [fpOf_ofSubst_congr ht htn 29 (by omega), fpOf_ofSubst_congr ht htn 32 (by omega),
      fpOf_ofSubst_congr ht htn 35 (by omega)]
  · simp only [sfTriple, rowPub, pubOfState]
    rw [fpOf_ofSubst_congr ht htn 38 (by omega), fpOf_ofSubst_congr ht htn 41 (by omega),
      fpOf_ofSubst_congr ht htn 44 (by omega)]

/-- **The decoded label is a function of the trace columns.** -/
theorem rowLabelVec_congr {E E' : Env K} (ht : E.trace = E'.trace)
    (htn : E.traceNext = E'.traceNext) : rowLabelVec E = rowLabelVec E' := by
  have hs := rowPub_s_congr ht htn
  have hf := rowPub_f_congr ht htn
  have he := rowPub_e_congr ht htn
  have hst := rowPub_state_congr ht
  funext k
  fin_cases k <;> simp only [rowLabelVec, labelVecOfPub, hs, hf, he, hst]

theorem rowTags_congr {E E' : Env K} (ht : E.trace = E'.trace)
    (htn : E.traceNext = E'.traceNext) : rowTags E = rowTags E' := by
  funext j
  simp only [rowTags, rowStateOf_congr ht]
  exact eval_congr_of_traceOnly _ (traceOnly_childTagHost _ j) ht htn

/-- **The declared child payloads are functions of the trace columns.** -/
theorem rowChildVec_congr {E E' : Env K} (ht : E.trace = E'.trace)
    (htn : E.traceNext = E'.traceNext) (l : ℕ) : rowChildVec E l = rowChildVec E' l := by
  have htags := rowTags_congr ht htn
  have hsf := rowPub_sfTriple_congr ht htn
  unfold rowChildVec
  match l with
  | 0 =>
      funext k
      fin_cases k <;> simp only [childVecN, childVec, htags, hsf 0]
  | 1 =>
      funext k
      fin_cases k <;> simp only [childVecN, childVec, htags, hsf 1]
  | 2 =>
      funext k
      fin_cases k <;> simp only [childVecN, childVec, htags, hsf 2]
  | n + 3 => rfl

theorem rowFanout_congr {E E' : Env K} (ht : E.trace = E'.trace) :
    rowFanout E = rowFanout E' := by
  simp only [rowFanout, rowStateOf_congr ht]

end RowDecoders

/-! ## 3. The `ℕ`-indexed walk operands of a committed compute table

Rows `1..N` read source row `i − 1` (the walk's row `i` is the table's row `i − 1`, as in
`Batch459.rowOf`); out-of-range rows read `0`. -/

section Operands
variable {K : Type} [Field K] {N : ℕ}

/-- `cur i = RLC^γ(label of row i)`. -/
def curOf (envs : Fin N → Env K) (γ : K) (i : ℕ) : K :=
  if h : 1 ≤ i ∧ i - 1 < N then rlc γ (rowLabelVec (envs ⟨i - 1, h.2⟩)) else 0

/-- `chld i l = RLC^γ(declared child payload l − 1 of row i)`. -/
def chldOf (envs : Fin N → Env K) (γ : K) (i l : ℕ) : K :=
  if h : 1 ≤ i ∧ i - 1 < N then rlc γ (rowChildVec (envs ⟨i - 1, h.2⟩) (l - 1)) else 0

/-- `fo i = fanout(state of row i)`. -/
def foOf (envs : Fin N → Env K) (i : ℕ) : ℕ :=
  if h : 1 ≤ i ∧ i - 1 < N then rowFanout (envs ⟨i - 1, h.2⟩) else 0

theorem foOf_le_three (envs : Fin N → Env K) (i : ℕ) : foOf envs i ≤ 3 := by
  unfold foOf
  split_ifs
  · exact rowFanout_le_three _
  · exact Nat.zero_le _

theorem curOf_succ (envs : Fin N → Env K) (γ : K) (k : ℕ) (hk : k < N) :
    curOf envs γ (k + 1) = rlc γ (rowLabelVec (envs ⟨k, hk⟩)) := by
  have h : 1 ≤ k + 1 ∧ k < N := ⟨by omega, hk⟩
  simp only [curOf, Nat.add_sub_cancel]
  rw [dif_pos h]

theorem chldOf_succ (envs : Fin N → Env K) (γ : K) (k l : ℕ) (hk : k < N) :
    chldOf envs γ (k + 1) l = rlc γ (rowChildVec (envs ⟨k, hk⟩) (l - 1)) := by
  have h : 1 ≤ k + 1 ∧ k < N := ⟨by omega, hk⟩
  simp only [chldOf, Nat.add_sub_cancel]
  rw [dif_pos h]

theorem foOf_succ (envs : Fin N → Env K) (k : ℕ) (hk : k < N) :
    foOf envs (k + 1) = rowFanout (envs ⟨k, hk⟩) := by
  have h : 1 ≤ k + 1 ∧ k < N := ⟨by omega, hk⟩
  simp only [foOf, Nat.add_sub_cancel]
  rw [dif_pos h]

end Operands

/-! ## 4. The root-difference polynomial and the paper's `α`-event

`rootDiffP cur chld fo root h = node_list_h(X) − node_queue_h^{root}(X)`, the queue started
at the **public** root (the paper with `RLC^γ(rvt_root)` in place of
`RLC^γ(current_node(1,·))`, which is what the seed `α · RLC^γ(rvt_root)` of `:962` injects). -/

section RootPolynomial
variable {K : Type} [Field K]

/-- `node_list_h(X) − node_queue_h^{root}(X)`. -/
def rootDiffP (cur : ℕ → K) (chld : ℕ → ℕ → K) (fo : ℕ → ℕ) (root : K) (h : ℕ) : K[X] :=
  nodeListP cur h - nodeQueueP (fun _ => root) chld fo h

/-- `deg ≤ max(h, 1 + Σ_{i≤h} fanout)`. -/
theorem rootDiffP_natDegree_le (cur : ℕ → K) (chld : ℕ → ℕ → K) (fo : ℕ → ℕ) (root : K)
    (h : ℕ) : (rootDiffP cur chld fo root h).natDegree ≤ max h (1 + Sf fo h) := by
  unfold rootDiffP
  refine (natDegree_sub_le _ _).trans ?_
  exact max_le_max (nodeListP_natDegree_le cur h) (nodeQueueP_natDegree_le _ chld fo h)

/-- `Σ_{i≤h} fanout ≤ 3h` when every fanout is `≤ 3`. -/
theorem Sf_le_three_mul {fo : ℕ → ℕ} (hfo : ∀ i, fo i ≤ 3) (h : ℕ) : Sf fo h ≤ 3 * h := by
  unfold Sf
  calc ∑ i ∈ Finset.Icc 1 h, fo i ≤ ∑ _i ∈ Finset.Icc 1 h, 3 :=
        Finset.sum_le_sum fun i _ => hfo i
    _ = 3 * h := by simp [Finset.sum_const, Nat.card_Icc]; ring

/-- **The degree majorant the tree proves: `3h + 1`**. -/
theorem rootDiffP_natDegree_le_three (cur : ℕ → K) (chld : ℕ → ℕ → K) {fo : ℕ → ℕ}
    (hfo : ∀ i, fo i ≤ 3) (root : K) (h : ℕ) :
    (rootDiffP cur chld fo root h).natDegree ≤ 3 * h + 1 := by
  refine (rootDiffP_natDegree_le cur chld fo root h).trans ?_
  have := Sf_le_three_mul hfo h
  exact max_le (by omega) (by omega)

/-- The bad coins of a polynomial: its roots when it is nonzero, nothing when it is zero. -/
def alphaBadOf [Fintype K] (D : K[X]) : Finset K :=
  if D = 0 then ∅ else Finset.univ.filter (fun a : K => D.eval a = 0)

theorem alphaBadOf_card_le [Fintype K] {D : K[X]} {d : ℕ} (hd : D.natDegree ≤ d) :
    (alphaBadOf D).card ≤ d := by
  unfold alphaBadOf
  split_ifs with h0
  · simp
  · exact (Walk.card_roots_le D h0).trans hd

/-- Outside the bad set, a vanishing evaluation forces the zero polynomial. -/
theorem eq_zero_of_eval_eq_zero_of_not_mem [Fintype K] {D : K[X]} {a : K}
    (ha : a ∉ alphaBadOf D) (heval : D.eval a = 0) : D = 0 := by
  by_contra hne
  apply ha
  simp [alphaBadOf, hne, heval]

/-- Inside the bad set: the polynomial is nonzero and vanishes there. -/
theorem mem_alphaBadOf_iff [Fintype K] {D : K[X]} {a : K} :
    a ∈ alphaBadOf D ↔ D ≠ 0 ∧ D.eval a = 0 := by
  unfold alphaBadOf
  split_ifs with h0 <;> simp [h0]

/-! ### The `X¹` coefficient reads the root -/

theorem nodeListP_coeff_one (cur : ℕ → K) {h : ℕ} (hh : 1 ≤ h) :
    (nodeListP cur h).coeff 1 = cur 1 := by
  unfold nodeListP
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h1
    exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hh⟩) h1

theorem queueTerm_coeff_one (chld : ℕ → ℕ → K) (fo : ℕ → ℕ) (i : ℕ) :
    (queueTerm chld fo i).coeff 1 = 0 := by
  unfold queueTerm
  rw [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro l hl
  rw [coeff_C_mul, coeff_X_pow]
  have hl1 := (Finset.mem_Icc.mp hl).1
  have : (1 : ℕ) ≠ 1 + l + Sf fo (i - 1) := by omega
  simp [this]

theorem nodeQueueP_coeff_one (cur : ℕ → K) (chld : ℕ → ℕ → K) (fo : ℕ → ℕ) (k : ℕ) :
    (nodeQueueP cur chld fo k).coeff 1 = cur 1 := by
  unfold nodeQueueP
  rw [coeff_add, finsetSum_coeff, coeff_C_mul, coeff_X_one]
  simp [queueTerm_coeff_one]

theorem rootDiffP_coeff_one (cur : ℕ → K) (chld : ℕ → ℕ → K) (fo : ℕ → ℕ) (root : K)
    {h : ℕ} (hh : 1 ≤ h) :
    (rootDiffP cur chld fo root h).coeff 1 = cur 1 - root := by
  unfold rootDiffP
  rw [coeff_sub, nodeListP_coeff_one cur hh, nodeQueueP_coeff_one]

/-- **The polynomial identity pins the root:** `node_list = node_queue^{root}` gives
`current_node(1,·) = rvt_root` at the `X¹` coefficient. -/
theorem cur_one_eq_root_of_rootDiffP_eq_zero {cur : ℕ → K} {chld : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {root : K} {h : ℕ} (hh : 1 ≤ h) (hD : rootDiffP cur chld fo root h = 0) :
    cur 1 = root := by
  have hc := rootDiffP_coeff_one cur chld fo root hh
  rw [hD, coeff_zero] at hc
  exact sub_eq_zero.mp hc.symm

/-! ### The walk telescoping with the seed left as the public root -/

variable {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {ln count acc : ℕ → K}
variable {α seed initial_count : K} {h : ℕ}

/-- `acc_closed` with `seed = root · α` for an arbitrary `root` (the paper's `:2293`
identification `root = current_node(1,·)` is **not** assumed):
`acc_walk(k) = −node_list_k(α) + node_queue_k^{root}(α)`. -/
theorem acc_closed_seeded (hw : WalkSat cur chld' fo ln count acc α seed initial_count h)
    (root : K) (hseed : seed = root * α) (hic : initial_count = α) :
    ∀ k, 1 ≤ k → k ≤ h →
      acc k = -(nodeListP cur k).eval α + (nodeQueueP (fun _ => root) chld' fo k).eval α := by
  intro k hk1 hkh
  rw [acc_telescope hw k hk1 hkh, nodeQueueP_eval, hseed, hic]
  have key : α * ∑ i ∈ Finset.Icc 1 k, childSum chld' fo α i
      = ∑ i ∈ Finset.Icc 1 k, ∑ l ∈ Finset.Icc 1 (fo i),
          chld' i l * α ^ (1 + l + Sf fo (i - 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold childSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp only [pow_add, pow_one]
    ring
  rw [key]
  ring

/-- **`Thm:Walk_IOP`'s root conclusion, at the recognizer inputs, outside the `α`-event.**
A walk satisfying the gates with `(seed, initial_count) = (root · α, α)` and `out_walk = 0`
 has `current_node(1,·) = root` unless `α` is a root of the nonzero
`rootDiffP` (`:2281` / `:2302`, the `h/|𝕂|` event). -/
theorem cur_one_eq_root_of_walkSat [Fintype K] {root : K}
    (hw : WalkSat cur chld' fo ln count acc α (root * α) α h)
    (hout : acc h = 0) (hα : α ∉ alphaBadOf (rootDiffP cur chld' fo root h)) :
    cur 1 = root := by
  have hcl := acc_closed_seeded hw root rfl rfl h hw.hpos le_rfl
  have heval : (rootDiffP cur chld' fo root h).eval α = 0 := by
    unfold rootDiffP
    rw [eval_sub]
    linear_combination hcl - hout
  exact cur_one_eq_root_of_rootDiffP_eq_zero hw.hpos (eq_zero_of_eval_eq_zero_of_not_mem hα heval)

end RootPolynomial

/-! ## 5. The `γ`-collision of two ten-coordinate labels (`Batch457::rootClaimBadGammas`) -/

section GammaCollision
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The coins at which two DISTINCT label vectors have the same `RLC^γ`; `∅` when equal. -/
def gammaBadOf (u v : Fin 10 → K) : Finset K :=
  if u = v then ∅ else Finset.univ.filter (fun γ : K => rlc γ u = rlc γ v)

/-- `≤ node_size − 1 = 9` (`Walk.rlc_collision_card_le`). -/
theorem gammaBadOf_card_le (u v : Fin 10 → K) : (gammaBadOf u v).card ≤ 9 := by
  unfold gammaBadOf
  split_ifs with huv
  · simp
  · exact (Walk.rlc_collision_card_le huv).trans (by norm_num)

/-- Outside the collision set, equal `RLC^γ` is equal labels. -/
theorem eq_of_rlc_eq_of_not_mem {u v : Fin 10 → K} {γ : K} (hγ : γ ∉ gammaBadOf u v)
    (heq : rlc γ u = rlc γ v) : u = v := by
  by_contra hne
  apply hγ
  simp [gammaBadOf, hne, heq]

end GammaCollision

/-! ## 6. The events on `JointCoins` and their fibre counts -/

section Fibres
variable {K : Type} [Fintype K] [DecidableEq K]

/-- A filter on the `αc` coordinate whose fibre over `(γ, αm, z)` has at most `d` elements has
at most `d · |𝕂|³` elements. -/
theorem card_filter_alphaC_le (bad : K → K × K → Finset K) (d : ℕ)
    (hb : ∀ g r, (bad g r).card ≤ d) :
    (Finset.univ.filter (fun ω : JointCoins K => alphaC ω ∈ bad (gamma ω) ω.2)).card ≤
      d * Fintype.card K ^ 3 := by
  have hsub : Finset.univ.filter (fun ω : JointCoins K => alphaC ω ∈ bad (gamma ω) ω.2) ⊆
      (Finset.univ : Finset (K × (K × K))).biUnion
        (fun t => (bad t.1 t.2).image (fun a => ((a, t.1), t.2))) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    refine Finset.mem_biUnion.mpr ⟨(ω.1.2, ω.2), Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨ω.1.1, hω, rfl⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine Finset.card_biUnion_le.trans ?_
  refine (Finset.sum_le_sum (fun t _ => Finset.card_image_le.trans (hb t.1 t.2))).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul]
  ring_nf
  exact le_rfl

/-- A filter on the `γ` coordinate whose fibre over `(αc, αm, z)` has at most `d` elements has
at most `d · |𝕂|³` elements. -/
theorem card_filter_gamma_le (bad : K → K × K → Finset K) (d : ℕ)
    (hb : ∀ a r, (bad a r).card ≤ d) :
    (Finset.univ.filter (fun ω : JointCoins K => gamma ω ∈ bad (alphaC ω) ω.2)).card ≤
      d * Fintype.card K ^ 3 := by
  have hsub : Finset.univ.filter (fun ω : JointCoins K => gamma ω ∈ bad (alphaC ω) ω.2) ⊆
      (Finset.univ : Finset (K × (K × K))).biUnion
        (fun t => (bad t.1 t.2).image (fun g => ((t.1, g), t.2))) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    refine Finset.mem_biUnion.mpr ⟨(ω.1.1, ω.2), Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨ω.1.2, hω, rfl⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine Finset.card_biUnion_le.trans ?_
  refine (Finset.sum_le_sum (fun t _ => Finset.card_image_le.trans (hb t.1 t.2))).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul]
  ring_nf
  exact le_rfl

end Fibres

section Events
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {N : ℕ}

/-- The paper's `:966` numeral `h`, recovered under the tiling (`rootDiffP_natDegree_le_of_tiling`).
The uniform degree majorant without tiling is `walkAlphaRootMajorant = 3N+1`. -/
def walkAlphaRootBound (N : ℕ) : ℕ := N

/-- The degree majorant the tree proves with no tiling: every compute fanout `≤ 3`. -/
def walkAlphaRootMajorant (N : ℕ) : ℕ := 3 * N + 1

/-- The numeral of the `γ`-event: `node_size − 1 = 9` for the ten-coordinate `LT_comp`. -/
def walkRootGammaBound : ℕ := 9

/-- The two walk-root summands the consumed bound gains over `|𝕂|` **under the tiling**
(`walkAlphaRootBound N + 9 = N+9`).  Compute/memory tiling events are priced separately
(`WalkTilingEvents`). -/
def walkRootBound (N : ℕ) : ℕ := walkAlphaRootBound N + walkRootGammaBound

theorem walkRootBound_eq (N : ℕ) : walkRootBound N = N + 9 := by
  simp [walkRootBound, walkAlphaRootBound, walkRootGammaBound]

omit [Fintype K] [DecidableEq K] in
/-- Under the paper's tiling `Σ fanout + 1 = h` the polynomial has degree `≤ h` — `:966`. -/
theorem rootDiffP_natDegree_le_of_tiling (cur : ℕ → K) (chld : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (root : K) {h : ℕ} (htile : Sf fo h + 1 = h) :
    (rootDiffP cur chld fo root h).natDegree ≤ h := by
  refine (rootDiffP_natDegree_le cur chld fo root h).trans ?_
  omega

/-- The `α`-bad set at `(γ, (αm, z))`: roots of `rootDiffP` with the public root
`RLC^γ(u z)` (`u z` = the claim's label vector at seed `z`). -/
def alphaBadAt (envs : Fin N → Env K) (u : K → Fin 10 → K) (g : K) (r : K × K) : Finset K :=
  alphaBadOf (rootDiffP (curOf envs g) (chldOf envs g) (foOf envs) (rlc g (u r.2)) N)

omit [DecidableEq K] in
theorem alphaBadAt_card_le_majorant (envs : Fin N → Env K) (u : K → Fin 10 → K)
    (g : K) (r : K × K) :
    (alphaBadAt envs u g r).card ≤ walkAlphaRootMajorant N :=
  alphaBadOf_card_le (rootDiffP_natDegree_le_three _ _ (foOf_le_three envs) _ _)

omit [DecidableEq K] in
/-- Under the tiling the paper's `h` is the degree (`:966`). -/
theorem alphaBadAt_card_le_of_tiling (envs : Fin N → Env K) (u : K → Fin 10 → K)
    (g : K) (r : K × K) (htile : Sf (foOf envs) N + 1 = N) :
    (alphaBadAt envs u g r).card ≤ walkAlphaRootBound N :=
  alphaBadOf_card_le (rootDiffP_natDegree_le_of_tiling _ _ _ _ htile)

omit [DecidableEq K] in
/-- Prefer `alphaBadAt_card_le_of_tiling` under the
queue gate. -/
theorem alphaBadAt_card_le (envs : Fin N → Env K) (u : K → Fin 10 → K) (g : K) (r : K × K) :
    (alphaBadAt envs u g r).card ≤ walkAlphaRootMajorant N :=
  alphaBadAt_card_le_majorant envs u g r

/-- **The `Thm:Walk_IOP` evaluation event on `αc`** of a committed
compute table `envs` against the claim's label `u`. -/
def alphaRootEvent (envs : Fin N → Env K) (u : K → Fin 10 → K) : Finset (JointCoins K) :=
  Finset.univ.filter (fun ω : JointCoins K => alphaC ω ∈ alphaBadAt envs u (gamma ω) ω.2)

theorem mem_alphaRootEvent_iff (envs : Fin N → Env K) (u : K → Fin 10 → K)
    (ω : JointCoins K) :
    ω ∈ alphaRootEvent envs u ↔
      alphaC ω ∈ alphaBadOf (rootDiffP (curOf envs (gamma ω)) (chldOf envs (gamma ω))
        (foOf envs) (rlc (gamma ω) (u (nprSeed ω))) N) := by
  simp only [alphaRootEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem card_alphaRootEvent_le (envs : Fin N → Env K) (u : K → Fin 10 → K) :
    (alphaRootEvent envs u).card ≤ walkAlphaRootMajorant N * Fintype.card K ^ 3 :=
  card_filter_alphaC_le _ _ (alphaBadAt_card_le_majorant envs u)

/-- The priced `α`-event: empty on a non-tiling table (the tiling event carries those coins),
the paper's degree-`h` root set on a tiled table. -/
def alphaRootEventConsumed (envs : Fin N → Env K) (u : K → Fin 10 → K) :
    Finset (JointCoins K) :=
  if Sf (foOf envs) N + 1 = N then alphaRootEvent envs u else ∅

theorem card_alphaRootEventConsumed_le (envs : Fin N → Env K) (u : K → Fin 10 → K) :
    (alphaRootEventConsumed envs u).card ≤ walkAlphaRootBound N * Fintype.card K ^ 3 := by
  unfold alphaRootEventConsumed
  split_ifs with htile
  · exact card_filter_alphaC_le _ _ (fun g r => alphaBadAt_card_le_of_tiling envs u g r htile)
  · simp

/-- The `γ`-bad set at `(αc, (αm, z))`: the collision coins of the claim's label at `z` with
the decoded root label `v`. -/
def gammaBadAt (u : K → Fin 10 → K) (v : Fin 10 → K) (_a : K) (r : K × K) : Finset K :=
  gammaBadOf (u r.2) v

/-- **The root/claim `γ`-collision event** (`Batch457::rootClaimBadGammas`, lifted). -/
def gammaRootEvent (u : K → Fin 10 → K) (v : Fin 10 → K) : Finset (JointCoins K) :=
  Finset.univ.filter (fun ω : JointCoins K => gamma ω ∈ gammaBadAt u v (alphaC ω) ω.2)

theorem mem_gammaRootEvent_iff (u : K → Fin 10 → K) (v : Fin 10 → K) (ω : JointCoins K) :
    ω ∈ gammaRootEvent u v ↔ gamma ω ∈ gammaBadOf (u (nprSeed ω)) v := by
  simp only [gammaRootEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem card_gammaRootEvent_le (u : K → Fin 10 → K) (v : Fin 10 → K) :
    (gammaRootEvent u v).card ≤ walkRootGammaBound * Fintype.card K ^ 3 :=
  card_filter_gamma_le _ _ (fun _ r => gammaBadOf_card_le (u r.2) v)

/-- **The compute walk's root events**, read off the committed table `envs`, the claim's
label `u` (a function of the NPR seed) and the decoded root label `v`.  The `α`-half is
the *consumed* event: empty unless the committed fanout tiles (`WalkTilingEvents` prices
the non-tiling coins). -/
def rootEvent (envs : Fin N → Env K) (u : K → Fin 10 → K) (v : Fin 10 → K) :
    Finset (JointCoins K) :=
  alphaRootEventConsumed envs u ∪ gammaRootEvent u v

theorem card_rootEvent_le (envs : Fin N → Env K) (u : K → Fin 10 → K) (v : Fin 10 → K) :
    (rootEvent envs u v).card ≤ walkRootBound N * Fintype.card K ^ 3 := by
  refine (Finset.card_union_le _ _).trans ?_
  rw [walkRootBound, add_mul]
  exact Nat.add_le_add (card_alphaRootEventConsumed_le envs u) (card_gammaRootEvent_le u v)

theorem notMem_rootEvent_iff (envs : Fin N → Env K) (u : K → Fin 10 → K) (v : Fin 10 → K)
    (ω : JointCoins K) :
    ω ∉ rootEvent envs u v ↔
      ω ∉ alphaRootEventConsumed envs u ∧ ω ∉ gammaRootEvent u v := by
  simp [rootEvent, not_or]

omit [Fintype K] [DecidableEq K] in
/-- `node_queue` reads `cur` only at `1`: with `cur 1 = root` the two queues coincide. -/
theorem nodeQueueP_const_root_eq {cur : ℕ → K} {chld : ℕ → ℕ → K} {fo : ℕ → ℕ} {root : K}
    (hcur : cur 1 = root) (k : ℕ) :
    nodeQueueP (fun _ => root) chld fo k = nodeQueueP cur chld fo k := by
  unfold nodeQueueP
  rw [hcur]

/-- **The honest exclusion, as a sufficient condition** (what a fixture or the generic
canonical-trace lemma has to supply): if the decoded root label IS the claim's label at the
seed and the decoded table is a full BFT at the coin `γ` (the paper's `node_list = node_queue`), then the coin is outside both root events.  The γ-half is
`∅` (equal labels); the α-half is `∅` because `rootDiffP` is the zero polynomial. -/
theorem notMem_rootEvent_of_root_eq_of_isFullBFT (envs : Fin N → Env K) (u : K → Fin 10 → K)
    (v : Fin 10 → K) (ω : JointCoins K) (hN : 0 < N)
    (hv : v = rowLabelVec (envs ⟨0, hN⟩))
    (hroot : u (nprSeed ω) = v)
    (hbft : IsFullBFT (curOf envs (gamma ω)) (chldOf envs (gamma ω)) (foOf envs) N) :
    ω ∉ rootEvent envs u v := by
  rw [notMem_rootEvent_iff]
  refine ⟨?_, ?_⟩
  · unfold alphaRootEventConsumed
    split_ifs with _htile
    · rw [mem_alphaRootEvent_iff]
      have hcur1 : curOf envs (gamma ω) 1 = rlc (gamma ω) (u (nprSeed ω)) := by
        rw [hroot, hv]
        exact curOf_succ envs (gamma ω) 0 hN
      have hD : rootDiffP (curOf envs (gamma ω)) (chldOf envs (gamma ω)) (foOf envs)
          (rlc (gamma ω) (u (nprSeed ω))) N = 0 := by
        unfold rootDiffP
        rw [nodeQueueP_const_root_eq hcur1, sub_eq_zero]
        exact hbft
      rw [hD]
      simp [alphaBadOf]
    · simp
  · rw [mem_gammaRootEvent_iff, hroot]
    simp [gammaBadOf]
/-- Membership reads `αc`, `γ` and `z` only (a cylinder along `αm`). -/
theorem rootEvent_alphaM_cylinder (envs : Fin N → Env K) (u : K → Fin 10 → K)
    (v : Fin 10 → K) (a g m m' z : K) :
    ((a, g), (m, z)) ∈ rootEvent envs u v ↔ ((a, g), (m', z)) ∈ rootEvent envs u v := by
  simp only [rootEvent, Finset.mem_union, alphaRootEventConsumed, mem_gammaRootEvent_iff]
  split_ifs
  · rw [mem_alphaRootEvent_iff, mem_alphaRootEvent_iff]
    simp [alphaC, gamma, nprSeed]
  · simp [alphaC, gamma, nprSeed]

end Events

end

end Nock.NockVMROM.Thm54.ComputeWalkRootEvents

#print axioms Nock.NockVMROM.Thm54.ComputeWalkRootEvents.traceOnly_semanticPub
#print axioms Nock.NockVMROM.Thm54.ComputeWalkRootEvents.rowLabelVec_congr
#print axioms Nock.NockVMROM.Thm54.ComputeWalkRootEvents.cur_one_eq_root_of_walkSat
#print axioms Nock.NockVMROM.Thm54.ComputeWalkRootEvents.card_rootEvent_le
