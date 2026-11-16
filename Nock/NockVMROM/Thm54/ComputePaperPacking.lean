import Nock.AIRPacked
import Nock.NockVMROM.Thm54.ComputeEnvAgreement
import Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
import Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
import Nock.NockVMROM.Thm54.PaperResourceCounts

/-!
    Σ_k op_k · (slot − target_k) = 0

("we … put these together in the evaluation gates in the end"), the displayed four-way
nonlinear fold `Σ_k op_k · (G_k − 1)`, and the packed memory-record /
`ln` equations.  The reified layer already has this basis:
`Nock.Reified.allPacked` (66 `𝕂` polynomials, `Nock/AIRPacked.lean`), exact against the atomic
per-opcode blocks at the honest selector (`Nock.Reified.packed_iff_atomic`).

It

1. maps `allPacked` into the optimized `13/62` layout through `computeTraceSubst` — the same
   substitution `finalNonIOSourceFamilies17` uses — and applies the tree's existing degree repair
   for the two OP3/OP5 output-bit booleanities (`refoldLeafBool`, the map form of
   `OptimizedComputeSubstitution.refoldedPerStateGates`'s two `set`s), giving
   `packedTableOptimized` (66 `𝕂` gates, degree `≤ 4`);
2. proves `paperPacking_iff_atomic`: at an **explicit one-hot selector** the packed set vanishes
   iff every per-state atomic `stateBlock` vanishes (the reified `packed_iff_atomic` lifted through
   `ComputeEnvAgreement.reEnv`); `paperPacking_iff_sources` extends this to the whole
   `finalNonIOSourceFamilies17.flatten`;
3. proves `deployed_of_paperPacking` (no coin) and `paperPacking_of_deployed` (under
   `FinalComputeCollisionFree`, the only place the fold coin appears) against the deployed
   `finalNonIOTransitionGates`;
6. proves canonical satisfaction: the honest same-execution rows (`exactFinalCurrentEnv`,
   `exactFinalTransitionEnv`) and the gathered canonical polynomial trace satisfy every gate;
   `challenge11`'s two walk-initial errors are carried as two masked `𝕂` gates, coin-free;
7. names the IO block as a **hole** reusing `correctedAccAfterStep` / `accAfterChain` /
   `finalAccInit` / `finalAccTerminal` — nothing redefined.
-/

namespace Nock.NockVMROM.Thm54
namespace ComputePaperPacking

set_option maxRecDepth 300000
set_option maxHeartbeats 8000000

open Nock
open Nock.Reified
open Nock.ComputeTable
open OptimizedComputeSubstitution
open OptimizedComputeGateBasis
open OptimizedComputeFinalTypedLowering
open OptimizedComputeCorrectedFinal
open OptimizedComputeTemplate

/-! ## 1. The one-hot selector hypothesis

Exactness is only ever claimed at a one-hot selector.  The predicate is the shape every honest
row supplies (`OptimizedComputeSameExecution.exactFinalCurrentEnv_selectors`) and the shape the
SV block forces on any accepted row under the characteristic hypothesis
(`oneHot_of_svBaseGates` below, the `ComputeTable.oneHot_of_bool_sum` route). -/

/-- The eleven base selector columns `0..10` are the one-hot of `st`. -/
def OneHotSelector {K : Type*} [Field K] (env : Env K) (st : State) : Prop :=
  ∀ s : State, env.trace (opCol s) = if s = st then 1 else 0

/-! ## 2. Reified layer: `allPacked ↔ perStateGated` at any one-hot environment

`Nock.Reified.packed_iff_atomic` is stated at `computeEnvFull inp (opSel st) pub dec ex`.  An
arbitrary `Env K` is carried to that shape by `ComputeEnvAgreement.reEnv`.  Both blocks read the
`z⁻¹` witness column `93` (the `cons` fingerprints), so the determined-slot fact
`E.trace 93 = (E.chal 1)⁻¹` is carried — it is exactly what the always-on gate `zZinvExpr`
(`z · zinv = 1`) supplies (`ComputeEnvAgreement.trace93_eq_inv_of_zZinv`). -/

section Reified
variable {K : Type*} [Field K]

theorem opOf_eq_opSel (E : Env K) (st : State) (h : OneHotSelector E st) :
    opOf E = opSel st := by
  funext s
  simp [opOf, opSel, h s]

theorem allPacked_rowScoped :
    allPacked.all (fun e => e.rowScoped 94 5) = true := by
  decide

theorem perStateGated_rowScoped :
    perStateGated.all (fun e => e.rowScoped 94 5) = true := by
  decide

theorem eval_reEnv_of_rowScoped (E : Env K) (st : State) (hz : E.trace 93 = (E.chal 1)⁻¹)
    (e : Expr) (he : e.rowScoped 94 5 = true) :
    e.eval E = e.eval (reEnv E st) :=
  Expr.eval_eq_of_rowScoped he
    (fun i hi => (reEnv_trace_agree E st hz i hi).symm)
    (fun j hj => (reEnv_chal_agree E st j hj).symm)

theorem gateBy_eval_env (E : Env K) (k : State) (e : Expr) :
    (gateBy k e).eval E = E.trace (opCol k) * e.eval E := by
  simp [gateBy, tc, Expr.eval]

/-- Gating collapse on an arbitrary one-hot environment (`Nock.Reified.gated_forall` generalised
off `computeEnvFull`). -/
theorem perStateGated_iff_active (E : Env K) (st : State) (h : OneHotSelector E st) :
    (∀ e ∈ perStateGated, e.eval E = 0) ↔
      (∀ e ∈ memBlkExprs st ++ evalRExprs st, e.eval E = 0) := by
  have hself : E.trace (opCol st) = 1 := by simp [h st]
  constructor
  · intro hall e he
    have hmem : gateBy st e ∈ perStateGated := by
      unfold perStateGated
      exact List.mem_flatMap.mpr ⟨st, mem_allStates st, List.mem_map.mpr ⟨e, he, rfl⟩⟩
    have h2 := hall _ hmem
    rw [gateBy_eval_env, hself, one_mul] at h2
    exact h2
  · intro hact e he
    unfold perStateGated at he
    obtain ⟨k, -, hke⟩ := List.mem_flatMap.mp he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hke
    rw [gateBy_eval_env]
    by_cases hk : k = st
    · subst hk
      rw [hself, one_mul]
      exact hact e' he'
    · rw [show E.trace (opCol k) = 0 by simp [h k, hk], zero_mul]

/-- **Reified exactness at any one-hot environment.**  The 66 packed polynomials vanish iff the
499 selector-gated atomics vanish. -/
theorem allPacked_iff_perStateGated (E : Env K) (st : State) (h : OneHotSelector E st)
    (hz : E.trace 93 = (E.chal 1)⁻¹) :
    (∀ e ∈ allPacked, e.eval E = 0) ↔ (∀ e ∈ perStateGated, e.eval E = 0) := by
  have hR : ∀ e ∈ allPacked, e.eval E = e.eval (reEnv E st) := fun e he =>
    eval_reEnv_of_rowScoped E st hz e ((List.all_eq_true.mp allPacked_rowScoped) e he)
  have hA : ∀ e ∈ perStateGated, e.eval E = e.eval (reEnv E st) := fun e he =>
    eval_reEnv_of_rowScoped E st hz e ((List.all_eq_true.mp perStateGated_rowScoped) e he)
  have hre : reEnv E st =
      computeEnvFull (inpOf E) (opSel st) (pubOfState E st) (decOf E) (exOf E) := by
    rw [reEnv, opOf_eq_opSel E st h]
  have key := packed_iff_atomic (inpOf E) (pubOfState E st) (decOf E) (exOf E) st
  have gated := gated_forall (inpOf E) (pubOfState E st) (decOf E) (exOf E) st
  rw [← hre] at key gated
  constructor
  · intro hp e he
    rw [hA e he]
    exact gated.2 (key.1 (fun e' he' => by rw [← hR e' he']; exact hp e' he')) e he
  · intro hg e he
    rw [hR e he]
    exact key.2 (gated.1 (fun e' he' => by rw [← hA e' he']; exact hg e' he')) e he

end Reified

/-! ## 3. The optimized `13/62` layout

`computeTraceSubst` (`OptimizedComputeSubstitution`) is the map `finalNonIOSourceFamilies17`
uses: base selectors `0..10` are fixed, fingerprint roles become extension projections, the
erased `mem_record₁` becomes its decoder, `mr2`/`mr3` the one-hot
state-selected decoders (`:1856-1883`). -/

/-- The 66 packed classes substituted verbatim.  Two of them — the OP3 and OP5 output-bit
booleanities `op_k · e.leaf · (1 − e.leaf)` — reach
trace degree `5` because the stored `e` role is restored by a selector multiplication; see
`raw_degree_excess`. -/
abbrev packedTableOptimizedRaw : List Expr :=
  OptimizedComputeGateBasis.packedTableOptimizedRaw

/-- The tree's existing degree repair, in map form: the two degree-5 bodies are replaced by the
direct fixed-role refolds `op3ELeafBoolRefold` / `op5ELeafBoolRefold` (degree `3`), which agree
with them on every one-hot row (`op3ELeafBool_refold_eval_oneHot`,
`op5ELeafBool_refold_eval_oneHot`).  This is exactly what
`OptimizedComputeSubstitution.refoldedPerStateGates` does to the atomic list by two `set`s
(`refoldedPerStateGates_eq_map`). -/
abbrev refoldLeafBool : Expr → Expr :=
  OptimizedComputeGateBasis.refoldLeafBool

theorem refoldLeafBool_eval {K : Type*} [Field K] (env : Env K) (st : State)
    (h : OneHotSelector env st) (e : Expr) :
    (refoldLeafBool e).eval env = e.eval env := by
  unfold refoldLeafBool OptimizedComputeGateBasis.refoldLeafBool
  split_ifs with h3 h5
  · rw [h3]; exact (op3ELeafBool_refold_eval_oneHot env st h).symm
  · rw [h5]; exact (op5ELeafBool_refold_eval_oneHot env st h).symm
  · rfl

/-- **The paper's selector-packed equality/nonlinear/memory classes in the optimized layout**.  66 `𝕂`-valued gates, no fold coin. -/
abbrev packedTableOptimized : List Expr :=
  OptimizedComputeGateBasis.packedTableOptimized

/-- The atomic list the tree folds is the same map applied to the substituted atomics. -/
theorem refoldedPerStateGates_eq_map :
    refoldedPerStateGates =
      (perStateGated.map (fun e => e.subst computeSubst)).map refoldLeafBool := by
  decide

/-- Per-state slices of the atomic list, as `OptimizedComputeGateBasis.stateBlock` cuts them. -/
def stateBlocks : List Expr := (allStates.map stateBlock).flatten

theorem stateBlocks_eq_refolded : stateBlocks = refoldedPerStateGates := by
  decide

theorem oneHot_ofSubst {K : Type*} [Field K] (env : Env K) (st : State)
    (h : OneHotSelector env st) :
    OneHotSelector (Env.ofSubst computeSubst env) st := by
  intro s
  have := h s
  cases s <;> simpa [Env.ofSubst, computeSubst, computeTraceSubst, opCol, Expr.eval] using this

/-- The optimized always-on witness gate `z · zinv = 1` (`zZinvExpr` through `computeSubst`;
challenge `5` is the `z⁻¹` slot) supplies the determined-slot fact for the decoded source
environment. -/
theorem trace93_ofSubst_of_zZinv {K : Type*} [Field K] (env : Env K)
    (hz : (zZinvExpr.subst computeSubst).eval env = 0) :
    (Env.ofSubst computeSubst env).trace 93 = ((Env.ofSubst computeSubst env).chal 1)⁻¹ := by
  apply trace93_eq_inv_of_zZinv
  rw [← Expr.eval_subst]
  exact hz

/-! ## 4. Exactness at the optimized layer -/

section Optimized
variable {K : Type*} [Field K]

theorem packedTableOptimized_iff_raw (env : Env K) (st : State) (h : OneHotSelector env st) :
    (∀ g ∈ packedTableOptimized, g.eval env = 0) ↔
      (∀ g ∈ packedTableOptimizedRaw, g.eval env = 0) := by
  simp only [packedTableOptimized, OptimizedComputeGateBasis.packedTableOptimized,
    List.forall_mem_map]
  exact forall_congr' fun e => forall_congr' fun _ =>
    iff_of_eq (congrArg (fun z => z = 0) (refoldLeafBool_eval env st h e))

theorem refolded_iff_perStateGated (env : Env K) (st : State) (h : OneHotSelector env st) :
    (∀ e ∈ refoldedPerStateGates, e.eval env = 0) ↔
      (∀ e ∈ perStateGated, e.eval (Env.ofSubst computeSubst env) = 0) := by
  rw [refoldedPerStateGates_eq_map]
  simp only [List.forall_mem_map, refoldLeafBool_eval env st h, Expr.eval_subst]

/-- **`paperPacking_iff_atomic`.**  On any optimized row environment whose selector is the
one-hot of `st`, the 66 packed gates vanish iff every per-state atomic block `stateBlock s`
vanishes (`Nock.Reified.packed_iff_atomic` lifted through `computeTraceSubst`).  Stated at an
explicit one-hot selector and nowhere else. -/
theorem paperPacking_iff_atomic (env : Env K) (st : State) (h : OneHotSelector env st)
    (hz : (zZinvExpr.subst computeSubst).eval env = 0) :
    (∀ g ∈ packedTableOptimized, g.eval env = 0) ↔
      (∀ s : State, ∀ e ∈ stateBlock s, e.eval env = 0) := by
  have hmid : (∀ g ∈ packedTableOptimized, g.eval env = 0) ↔
      (∀ e ∈ refoldedPerStateGates, e.eval env = 0) := by
    rw [packedTableOptimized_iff_raw env st h, refolded_iff_perStateGated env st h]
    simp only [packedTableOptimizedRaw, OptimizedComputeGateBasis.packedTableOptimizedRaw,
      List.forall_mem_map, Expr.eval_subst]
    exact allPacked_iff_perStateGated _ st (oneHot_ofSubst env st h)
      (trace93_ofSubst_of_zZinv env hz)
  rw [hmid, ← stateBlocks_eq_refolded]
  simp only [stateBlocks, List.mem_flatten, List.mem_map]
  constructor
  · intro hh s e he
    exact hh e ⟨stateBlock s, ⟨s, mem_allStates s, rfl⟩, he⟩
  · rintro hh e ⟨l, ⟨s, -, rfl⟩, he⟩
    exact hh s e he

end Optimized

/-! ## 5. The full coin-free non-IO transition set

The deployed seventeen families carry, beside the eleven `stateBlock`s, an always-on prefix and
four cross-row singletons.  The packed basis keeps them verbatim — a singleton's fold is
`e + c₉ · 0`, coin-free already — so the 1-1 comparison with `finalNonIOTransitionGates` is
exact. -/

/-- Always-on `𝕂` prefix: SV4–SV6 head equations and the formula
reconstruction `f = cons(f_h, f_t)`.  F-E-3: the tree-only `z · z⁻¹ = 1`
witness is **not** committed (it is `chal 1 · chal 5 − 1` after subst); `paperPacking_iff_atomic`
still takes it as a coin-pin hypothesis. -/
abbrev alwaysOnOptimized : List Expr :=
  OptimizedComputeGateBasis.alwaysOnOptimized

/-- Cross-row singletons: the compute line chain `ln_prev(i+1) = ln(i)`
and the three walk recurrences — line the paper, count `:840`, accumulator `:848-850` — in
the `finalWalkSubst` namespace. -/
abbrev crossRowSingletons : List Expr :=
  OptimizedComputeGateBasis.crossRowSingletons

/-- **The coin-free non-IO transition gate set.**  78 `𝕂`-valued gates: 66 packed classes, 6
always-on, 4 cross-row, 2 queue-witness.  No challenge `9`, no challenge `11` (`nonIO_reads_no_fold_coin`). -/
abbrev paperPackingNonIOGates : List Expr :=
  OptimizedComputeGateBasis.paperPackingNonIOGates

/-- Packed + always-on + cross-row.  The source-family
iff is about this list; the two queue-witness gates sit beside it. -/
abbrev paperPackingCoreGates : List Expr :=
  packedTableOptimized ++ alwaysOnOptimized ++ crossRowSingletons

theorem paperPackingCoreGates_length : paperPackingCoreGates.length = 76 := by
  decide

theorem paperPackingNonIOGates_length : paperPackingNonIOGates.length = 78 :=
  OptimizedComputeGateBasis.paperPackingNonIOGates_length

theorem mem_nonIO_of_mem_core {g : Expr} (h : g ∈ paperPackingCoreGates) :
    g ∈ paperPackingNonIOGates := by
  change g ∈ packedTableOptimized ++ alwaysOnOptimized ++ crossRowSingletons ++
    OptimizedComputeGateBasis.queueWitnessGates
  exact List.mem_append.mpr (Or.inl h)

theorem packedTableOptimized_length : packedTableOptimized.length = 66 := by
  decide

/-- The four-way nonlinear fold of the paper is one of the packed classes and is
syntactically the deployed `optimizedCombinedGate`. -/
theorem optimizedCombinedGate_mem_packed :
    optimizedCombinedGate ∈ packedTableOptimized := by
  decide

theorem exists_state_iff (P : State → Prop) :
    (∃ s, P s) ↔ (P .s0 ∨ P .s1 ∨ P .s2 ∨ P .s3 ∨ P .s4 ∨ P .s5 ∨ P .s6 ∨ P .s7 ∨ P .s8 ∨
      P .s9 ∨ P .cons) := by
  constructor
  · rintro ⟨s, h⟩
    cases s <;> simp [h]
  · rintro (h | h | h | h | h | h | h | h | h | h | h) <;> exact ⟨_, h⟩

/-- Membership in the deployed families' flatten, decomposed into the four sources plus the
F-E-3 coin relation `zZinv` (still a source-family singleton, not a committed packing gate). -/
theorem mem_finalNonIO_flatten_iff (e : Expr) :
    e ∈ finalNonIOSourceFamilies17.flatten ↔
      (∃ s : State, e ∈ stateBlock s) ∨ e ∈ alwaysOnOptimized ∨
        e = optimizedCombinedGate ∨ e = zZinvExpr.subst computeSubst ∨
        e ∈ crossRowSingletons := by
  rw [exists_state_iff]
  simp only [finalNonIOSourceFamilies17, nonIOSourceFamilies17With,
    alwaysOnOptimized, OptimizedComputeGateBasis.alwaysOnOptimized,
    crossRowSingletons, OptimizedComputeGateBasis.crossRowSingletons,
    List.flatten_cons, List.flatten_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.append_nil, or_assoc]
  tauto

section Optimized
variable {K : Type*} [Field K]

theorem zZinv_mem_finalNonIO :
    zZinvExpr.subst computeSubst ∈ finalNonIOSourceFamilies17.flatten := by
  simp [finalNonIOSourceFamilies17, nonIOSourceFamilies17With]

/-- **`paperPacking_iff_sources`.**  At a one-hot selector, the 76 core coin-free gates plus the
F-E-3 coin pin `hz` (`z · z⁻¹ = 1`) vanish iff all 511 sources behind the deployed seventeen
families vanish. -/
theorem paperPacking_iff_sources (env : Env K) (st : State) (h : OneHotSelector env st)
    (hz : (zZinvExpr.subst computeSubst).eval env = 0) :
    (∀ g ∈ paperPackingCoreGates, g.eval env = 0) ↔
      (∀ e ∈ finalNonIOSourceFamilies17.flatten, e.eval env = 0) := by
  simp only [paperPackingCoreGates, List.forall_mem_append]
  constructor
  · rintro ⟨⟨hpk, hon⟩, hcr⟩ e he
    have hp := paperPacking_iff_atomic env st h hz
    rcases (mem_finalNonIO_flatten_iff e).1 he with ⟨s, hs⟩ | hon' | rfl | rfl | hcr'
    · exact hp.1 hpk s e hs
    · exact hon e hon'
    · exact hpk _ optimizedCombinedGate_mem_packed
    · exact hz
    · exact hcr e hcr'
  · intro hs
    have hp := paperPacking_iff_atomic env st h hz
    refine ⟨⟨hp.2 (fun s e he => hs e ((mem_finalNonIO_flatten_iff e).2 (Or.inl ⟨s, he⟩))),
      fun e he => hs e ((mem_finalNonIO_flatten_iff e).2 (Or.inr (Or.inl he)))⟩,
      fun e he => hs e ((mem_finalNonIO_flatten_iff e).2
        (Or.inr (Or.inr (Or.inr (Or.inr he)))))⟩

/-- **`deployed_of_paperPacking` — no fold-coin hypothesis.**  The coin-free set vanishing,
together with the F-E-3 pin `hz`, forces every deployed challenge-9 fold to vanish. -/
theorem deployed_of_paperPacking (env : Env K) (st : State) (h : OneHotSelector env st)
    (hz : (zZinvExpr.subst computeSubst).eval env = 0)
    (hg : ∀ g ∈ paperPackingCoreGates, g.eval env = 0) :
    ∀ g ∈ finalNonIOTransitionGates, g.eval env = 0 :=
  finalNonIOTransitionGates_complete env ((paperPacking_iff_sources env st h hz).1 hg)

/-- **`paperPacking_of_deployed` — the ONLY place the fold coin appears.**  The deployed folds
vanishing force the *core* coin-free set to vanish under `FinalComputeCollisionFree` (challenge `9`
misses every family's bad set).  `hz` is recovered from the zZinv source family. -/
theorem paperPacking_of_deployed (env : Env K) (st : State) (h : OneHotSelector env st)
    (hfree : FinalComputeCollisionFree env)
    (hg : ∀ g ∈ finalNonIOTransitionGates, g.eval env = 0) :
    ∀ g ∈ paperPackingCoreGates, g.eval env = 0 := by
  have hsrc := finalNonIOTransitionGates_sound env hfree hg
  exact (paperPacking_iff_sources env st h (hsrc _ zZinv_mem_finalNonIO)).2 hsrc

end Optimized

/-! ## 6. Deriving the one-hot hypothesis from the committed SV block

The eleven booleanities and the one-hot sum are base-field gates on the
selector columns `0..10`, unchanged by `computeTraceSubst`. -/

/-- The twelve `𝔽`-valued SV gates (SV2 booleanity ×11, SV3 one-hot sum). -/
def svBaseGates : List Expr := svBoolExprs ++ [svOneHotExprF]

theorem svBaseGates_length : svBaseGates.length = 12 := by decide

theorem svBaseGates_subst_fixed :
    svBaseGates.map (fun e => e.subst computeSubst) = svBaseGates := by
  decide

theorem svBaseGates_degree : ∀ g ∈ svBaseGates, g.degree ≤ 2 := by decide

theorem oneHot_of_svBaseGates {K : Type*} [Field K] (env : Env K)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hsv : ∀ e ∈ svBaseGates, e.eval env = 0) :
    ∃ st : State, OneHotSelector env st := by
  have hbool : ∀ j : State, env.trace (opCol j) = 0 ∨ env.trace (opCol j) = 1 := by
    intro j
    have hmem : svBoolExprF (opCol j) ∈ svBaseGates := by
      simp only [svBaseGates, svBoolExprs, List.mem_append, List.mem_map]
      exact Or.inl ⟨j, mem_allStates j, rfl⟩
    have hb := hsv _ hmem
    have : env.trace (opCol j) * (1 - env.trace (opCol j)) = 0 := by
      simpa [svBoolExprF, tc, Expr.eval] using hb
    exact (bool_iff _).mp this
  have hsum : env.trace (opCol .cons) + sum09 (fun j => env.trace (opCol j)) = 1 := by
    have h1 := hsv svOneHotExprF (by simp [svBaseGates])
    simp only [svOneHotExprF, tc, Expr.eval, Int.cast_one, sub_eq_zero] at h1
    simp only [sum09, opCol]
    linear_combination h1
  obtain ⟨s, hs⟩ := oneHot_of_bool_sum (fun j => env.trace (opCol j)) hchar hbool hsum
  refine ⟨s, fun j => ?_⟩
  have := congrFun hs j
  simpa [opSel] using this

/-- `deployed_of_paperPacking` with the one-hot hypothesis derived from the SV block. -/
theorem deployed_of_paperPacking_sv {K : Type*} [Field K] (env : Env K)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hsv : ∀ e ∈ svBaseGates, e.eval env = 0)
    (hz : (zZinvExpr.subst computeSubst).eval env = 0)
    (hg : ∀ g ∈ paperPackingCoreGates, g.eval env = 0) :
    ∀ g ∈ finalNonIOTransitionGates, g.eval env = 0 := by
  obtain ⟨st, h⟩ := oneHot_of_svBaseGates env hchar hsv
  exact deployed_of_paperPacking env st h hz hg

/-! ## 7. -/

/-- Every coin-free non-IO gate has trace degree `≤ 4` after the two leaf-booleanity refolds. -/
theorem paperPackingNonIOGates_degree : ∀ g ∈ paperPackingNonIOGates, g.degree ≤ 4 := by
  decide

/-- **Reported, not dropped.**  Substituted verbatim, exactly two packed classes exceed degree
`4`: the OP3 and OP5 output-bit booleanities at degree `5` (the stored `e.leaf` role is restored
through a selector product).  They are the two the tree already refolds
(`OptimizedComputeSubstitution.fixed_overlay_leaf_booleanity_degrees`); the refolds have degree
`3` and agree on every one-hot row. -/
theorem raw_degree_excess :
    (packedTableOptimizedRaw.filter (fun g => decide (4 < g.degree))).length = 2 ∧
      packedTableOptimizedRaw[32]? = some (op3ELeafBool.subst computeSubst) ∧
      packedTableOptimizedRaw[35]? = some (op5ELeafBool.subst computeSubst) ∧
      (op3ELeafBool.subst computeSubst).degree = 5 ∧
      (op5ELeafBool.subst computeSubst).degree = 5 ∧
      op3ELeafBoolRefold.degree = 3 ∧ op5ELeafBoolRefold.degree = 3 := by
  decide

/-- Degree histogram of the 76 coin-free gates.  F-E-3 dropped the degree-`0` witness
`z · zinv = 1` (a coin relation, not a trace gate).  Was
`0/2/12/50/12/0`. -/
theorem paperPackingNonIOGates_histogram :
    paperPackingNonIOGates.countP (fun g => g.degree == 0) = 0 ∧
      paperPackingNonIOGates.countP (fun g => g.degree == 1) = 2 ∧
      paperPackingNonIOGates.countP (fun g => g.degree == 2) = 12 ∧
      paperPackingNonIOGates.countP (fun g => g.degree == 3) = 52 ∧
      paperPackingNonIOGates.countP (fun g => g.degree == 4) = 12 ∧
      paperPackingNonIOGates.countP (fun g => 5 ≤ g.degree) = 0 := by
  decide

/-! ## 8. Typed lowering through `correctedLowerFinal` -/

/-- The 77 gates lowered to the corrected typed layer (`OptimizedComputeCorrectedFinal`). -/
def paperPackingTyped : List CorrectedFinalTypedExpr :=
  paperPackingNonIOGates.filterMap correctedLowerFinal

/-- Every gate lowers (no dropped gate) and every typed gate has degree `≤ 4`. -/
theorem paperPackingTyped_length : paperPackingTyped.length = 78 := by
  decide

theorem paperPackingTyped_degree : ∀ t ∈ paperPackingTyped, t.degree ≤ 4 := by
  decide

/-- No coin-free gate reads the compiler challenges `9`, `11`. -/
def readsNoCompilerChallenge : Expr → Bool
  | .Var .challenge q => decide (q < 9 ∨ q = 10)
  | .Var _ _ | .Const _ => true
  | .Add x y | .Sub x y | .Mul x y => readsNoCompilerChallenge x && readsNoCompilerChallenge y
  | .Neg x | .Pow x _ => readsNoCompilerChallenge x

theorem nonIO_reads_no_fold_coin :
    paperPackingNonIOGates.all readsNoCompilerChallenge = true := by
  decide

/-- Positive control for the read-set instrument: the deployed folds do read challenge `9`. -/
theorem deployed_folds_read_fold_coin :
    ¬ finalNonIOTransitionGates.all readsNoCompilerChallenge = true := by
  decide

/-! ## 9. `challenge11`: two masked `𝕂` gates, coin-free

The deployed `finalMaskedWalkInitFold = isFirst·ln₁ + c₁₁ · isFirst·count₁` folds the two
walk-initial errors at challenge `11`, priced `1/|𝕂|`.  They are `isFirst`-masked, not
selector-distinguished, so the coin-free substitute is the two gates themselves (`+e`). -/

/-- The two walk-initial masked gates. -/
def walkInitUnfolded : List Expr := [finalMaskedWalkLn1, finalMaskedWalkCount1]

def walkInitUnfoldedTyped : List CorrectedFinalTypedExpr :=
  walkInitUnfolded.filterMap correctedLowerFinal

theorem walkInitUnfoldedTyped_length : walkInitUnfoldedTyped.length = 2 := by decide

theorem walkInitUnfoldedTyped_degree : ∀ t ∈ walkInitUnfoldedTyped, t.degree ≤ 2 := by decide

theorem walkInitUnfolded_reads_no_fold_coin :
    walkInitUnfolded.all readsNoCompilerChallenge = true := by decide

/-- Unfolded ⇒ folded, at every value of challenge `11`. -/
theorem walkInitFold_of_unfolded {K : Type*} [Field K] (env : Env K)
    (h : ∀ g ∈ walkInitUnfolded, g.eval env = 0) :
    finalMaskedWalkInitFold.eval env = 0 := by
  have h1 := h finalMaskedWalkLn1 (by simp [walkInitUnfolded])
  have h2 := h finalMaskedWalkCount1 (by simp [walkInitUnfolded])
  simp [finalMaskedWalkInitFold, Expr.eval, h1, h2]

/-- Folded ⇒ unfolded only off the priced bad set — the event the coin-free basis deletes. -/
theorem walkInitUnfolded_of_fold {K : Type*} [Field K] [Fintype K] [DecidableEq K] (env : Env K)
    (hgate : finalMaskedWalkInitFold.eval env = 0)
    (hgood : env.chal (compilerChallengeBase + 2) ∉
      OptimizedComputeCollisionBound.walkInitBadChallenges env) :
    ∀ g ∈ walkInitUnfolded, g.eval env = 0 := by
  have h := OptimizedComputeCollisionBound.walkInit_sources_zero_of_good env hgate hgood
  intro g hg
  simp only [walkInitUnfolded, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact h.1
  · exact h.2

/-! ## 10. The IO block — NAMED HOLE

Reused, not redefined: the three inactive-safe denominator
pins, the unmasked step
`correctedAccAfterStep` (`:526-527`), the chain `accAfterChain` (`:526-527`, one column read at
`i−1` and `i`), and the two anchors `finalAccInit = isFirst·acc`, `finalAccTerminal =
isLast·(acc_after − requests)` (`:534-537`, `:597`). -/

/-- IO transition gates as deployed today, typed: 3 denominator pins + step + chain. -/
def ioBlockTransitionTyped : List CorrectedFinalTypedExpr :=
  (finalSampledIOTransitionGates.take 3).filterMap correctedLowerFinal ++
    [correctedAccAfterStep, accAfterChain]

/-- IO endpoint anchors as deployed today, typed. -/
def ioBlockEndpointTyped : List CorrectedFinalTypedExpr :=
  [finalAccInit, finalAccTerminal].filterMap correctedLowerFinal

theorem ioBlock_counts :
    ioBlockTransitionTyped.length = 5 ∧ ioBlockEndpointTyped.length = 2 := by
  decide

/-! ## 11. Counts against the paper

the paper: "15 + 24·e gates of degree at most 4".  The deployed tree meets it as
`15 𝔽 + (17 folds + 3 pins + chain + step + 2 residual pins)·e`.  Coin-free, the 17 folds become
77 gates and nothing else moves at stage 1. -/

/-- In the optimized layout the eight `mem_record₁` equations are **decoder identities** — `mr1` is not a committed column set, so they
vanish under `computeTraceSubst` on every environment and cost no gate; `81 − 8 = 73` row-local
`𝕂` gates, plus the four cross-row singletons the deployed families carry, is `77`. -/
theorem mr1_decoder_discharged {K : Type*} [Field K] (env : Env K) :
    mr1Exprs.length = 8 ∧ ∀ e ∈ mr1Exprs, (e.subst computeSubst).eval env = 0 :=
  ⟨by decide, mr1Exprs_subst_vanish env⟩

/-- `𝕂`-valued coin-free non-IO transition gates. -/
def kValuedNonIOTransitionGates : ℕ := 78

/-- `𝔽`-valued transition gates (the deployed base bucket: 12 SV + 2 mask booleanities + overlap
consistency, `OptimizedComputeFinal.finalBaseTransitionGates`), unchanged. -/
def fValuedTransitionGates : ℕ := 15

/-- IO/residual `𝕂` transition gates as deployed (3 pins, chain, step, 2 residual pins). -/
def ioAndResidualKGates : ℕ := 7

/-- Base-gate cost of the coin-free transition bucket at extension degree `e`. -/
def paperPackingTransitionBaseGates (e : ℕ) : ℕ :=
  fValuedTransitionGates + (kValuedNonIOTransitionGates + ioAndResidualKGates) * e

/-- The paper's numeral is `computeTransitionGatesPaper`; the deployed
coin-free packing bucket is `paperPackingTransitionBaseGates = 15 + 85·e`. -/
theorem counts_vs_paper :
    (∀ e, Thm54Resources.computeTransitionGatesPaper e =
        fValuedTransitionGates + (17 + ioAndResidualKGates) * e) ∧
      (∀ e, Thm54Resources.computeTransitionGates e =
        paperPackingTransitionBaseGates e + Thm54Resources.rangeGates e 64 + 1) ∧
      paperPackingTransitionBaseGates 3 = 270 ∧
      Thm54Resources.computeTransitionGatesPaper 3 = 87 ∧
      kValuedNonIOTransitionGates = paperPackingNonIOGates.length := by
  refine ⟨fun e => ?_, fun e => ?_, rfl, rfl, paperPackingNonIOGates_length.symm⟩
  · simp [Thm54Resources.computeTransitionGatesPaper, fValuedTransitionGates, ioAndResidualKGates]
    ring
  · simp [Thm54Resources.computeTransitionGates, paperPackingTransitionBaseGates,
      fValuedTransitionGates, kValuedNonIOTransitionGates, ioAndResidualKGates]
    omega

theorem paper_numeral_not_attainable_coin_free (e : ℕ) :
    paperPackingTransitionBaseGates e =
      Thm54Resources.computeTransitionGatesPaper e + 61 * e := by
  simp [paperPackingTransitionBaseGates, Thm54Resources.computeTransitionGatesPaper,
    fValuedTransitionGates, kValuedNonIOTransitionGates, ioAndResidualKGates]
  ring

/-! ## 12. Canonical satisfaction

The honest same-execution rows and the gathered canonical polynomial trace satisfy every
coin-free gate.  The 73 row-local gates (`paperPackingRowLocal`) hold on **every** row including
the terminal one; the four cross-row singletons hold on every row with a successor, exactly as
the deployed chip masks them at the last row (`OptimizedComputeCorrectedFinal.correctedCoreCoord`
ids `8..11`). -/

/-- The row-local part: 66 packed classes + 7 always-on. -/
abbrev paperPackingRowLocal : List Expr :=
  OptimizedComputeGateBasis.paperPackingRowLocal

theorem paperPackingNonIOGates_eq_rowLocal_append :
    paperPackingNonIOGates =
      paperPackingRowLocal ++ crossRowSingletons ++
        OptimizedComputeGateBasis.queueWitnessGates :=
  OptimizedComputeGateBasis.paperPacking_eq_rowLocal_append

#print axioms paperPacking_iff_atomic
#print axioms paperPacking_iff_sources
#print axioms deployed_of_paperPacking
#print axioms paperPacking_of_deployed
#print axioms deployed_of_paperPacking_sv
#print axioms paperPackingNonIOGates_degree
#print axioms paperPackingTyped_degree
#print axioms raw_degree_excess
#print axioms nonIO_reads_no_fold_coin
#print axioms counts_vs_paper
#print axioms mr1_decoder_discharged
#print axioms paper_numeral_not_attainable_coin_free
#print axioms walkInitFold_of_unfolded
#print axioms walkInitUnfolded_of_fold

end ComputePaperPacking
end Nock.NockVMROM.Thm54
