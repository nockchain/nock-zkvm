/-
  Nock/NockVMROM/Thm54/BelowDefs/P8Core/OptimizedHostileTimestamps.lean

  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/P8Core/OptimizedHostileTimestamps.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs` or the statement file, directly or transitively.
-/
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.OptimizedHostileIOAssembly

namespace Nock.NockVMROM.Thm54

namespace FiniteIO

open Polynomial
open scoped BigOperators
variable {K : Type*} [Field K] {m : ℕ} [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]

/-- The sampled-pole identity, outside event (3), lifts to the symbolic log-derivative identity
in `K(X)` (the first half of the proof of `finiteIO_sound_of_identity`, factored out). -/
theorem frac_identity_of_pole_identity (records : PreChallengeRecords K m)
    (coins : IOCoins K)
    (hdA : ∀ i, coins.pole + reqVals records coins.gamma i ≠ 0)
    (hdB : ∀ j, coins.pole + respVals records coins.gamma j ≠ 0)
    (hend : (∑ i, (coins.pole + reqVals records coins.gamma i)⁻¹) =
      ∑ j, (coins.pole + respVals records coins.gamma j)⁻¹)
    (hpole : coins.pole ∉ IOLogDerivEvent records coins.gamma) :
    (∑ i, SetEq.frac (reqVals records coins.gamma i)) =
      ∑ j, SetEq.frac (respVals records coins.gamma j) := by
  classical
  set A := reqVals records coins.gamma with hA
  set B := respVals records coins.gamma with hB
  have hQeval : (ioQP records coins.gamma).eval coins.pole = 0 := by
    have hSA := sum_inv_eval A coins.pole hdA
    have hSB := sum_inv_eval B coins.pole hdB
    simp only [ioQP, Polynomial.eval_sub, Polynomial.eval_mul, ← hA, ← hB]
    have h1 : (numerP A).eval coins.pole * (denomP B).eval coins.pole
        = ((∑ i, (coins.pole + A i)⁻¹) * (denomP A).eval coins.pole)
            * (denomP B).eval coins.pole := by rw [hSA]
    have h2 : (numerP B).eval coins.pole * (denomP A).eval coins.pole
        = ((∑ j, (coins.pole + B j)⁻¹) * (denomP B).eval coins.pole)
            * (denomP A).eval coins.pole := by rw [hSB]
    rw [h1, h2, hend]
    ring
  have hQ : ioQP records coins.gamma = 0 := by
    by_contra hQ0
    exact hpole (by
      simp only [IOLogDerivEvent, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hQ0, hQeval⟩)
  have hQ' : numerP A * denomP B = numerP B * denomP A := by
    have hh := hQ
    unfold ioQP at hh
    rw [← hA, ← hB, sub_eq_zero] at hh
    exact hh
  have hmapQ : algebraMap K[X] (RatFunc K) (numerP A) * algebraMap K[X] (RatFunc K) (denomP B)
      = algebraMap K[X] (RatFunc K) (numerP B) * algebraMap K[X] (RatFunc K) (denomP A) := by
    rw [← map_mul, ← map_mul, hQ']
  have hdAne : algebraMap K[X] (RatFunc K) (denomP A) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective K)]
    exact denomP_ne_zero A
  have hdBne : algebraMap K[X] (RatFunc K) (denomP B) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective K)]
    exact denomP_ne_zero B
  have hA' := frac_sum_mul_denom A
  have hB' := frac_sum_mul_denom B
  have hkey : (∑ i, SetEq.frac (A i))
        * (algebraMap K[X] (RatFunc K) (denomP A) * algebraMap K[X] (RatFunc K) (denomP B))
      = (∑ j, SetEq.frac (B j))
        * (algebraMap K[X] (RatFunc K) (denomP A) * algebraMap K[X] (RatFunc K) (denomP B)) := by
    calc (∑ i, SetEq.frac (A i))
          * (algebraMap K[X] (RatFunc K) (denomP A) * algebraMap K[X] (RatFunc K) (denomP B))
        = ((∑ i, SetEq.frac (A i)) * algebraMap K[X] (RatFunc K) (denomP A))
            * algebraMap K[X] (RatFunc K) (denomP B) := by ring
      _ = algebraMap K[X] (RatFunc K) (numerP A) * algebraMap K[X] (RatFunc K) (denomP B) := by
            rw [hA']
      _ = algebraMap K[X] (RatFunc K) (numerP B) * algebraMap K[X] (RatFunc K) (denomP A) :=
            hmapQ
      _ = ((∑ j, SetEq.frac (B j)) * algebraMap K[X] (RatFunc K) (denomP B))
            * algebraMap K[X] (RatFunc K) (denomP A) := by rw [hB']
      _ = (∑ j, SetEq.frac (B j))
            * (algebraMap K[X] (RatFunc K) (denomP A)
                * algebraMap K[X] (RatFunc K) (denomP B)) := by ring
  exact mul_right_cancel₀ (mul_ne_zero hdAne hdBne) hkey

/-- **`cor_uni_req_uni_resp` at the identity.**  If the
requests are `Nodup`, the identity forces the responses to be `Nodup` too: the log-derivative
identity is an equality of value *multisets* (`SetEq.mse_ldse_general`), a multiset equal to a
`Nodup` one is `Nodup`, and RLC injectivity outside event (2) carries this back to the records. -/
theorem responses_nodup_of_identity {Ksz : ℕ} (records : PreChallengeRecords K m)
    (coins : IOCoins K)
    (hdA : ∀ i, coins.pole + reqVals records coins.gamma i ≠ 0)
    (hdB : ∀ j, coins.pole + respVals records coins.gamma j ≠ 0)
    (hend : (∑ i, (coins.pole + reqVals records coins.gamma i)⁻¹) =
      ∑ j, (coins.pole + respVals records coins.gamma j)⁻¹)
    (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz records.requests.length)
    (hKresp : records.responses.length ≤ Ksz)
    (hreqnd : records.requests.Nodup)
    (hγ : coins.gamma ∉ IORLCCollisionEvent records)
    (hpole : coins.pole ∉ IOLogDerivEvent records coins.gamma) :
    records.responses.Nodup := by
  classical
  set A := reqVals records coins.gamma with hA
  set B := respVals records coins.gamma with hB
  have hfrac : (∑ i, SetEq.frac (A i)) = ∑ j, SetEq.frac (B j) :=
    frac_identity_of_pole_identity records coins hdA hdB hend hpole
  have hn₁ : records.requests.length < p := lt_of_le_of_lt hKreq.2 hKp
  have hn₂ : records.responses.length < p := lt_of_le_of_lt hKresp hKp
  have hmulti : SetEq.valMultiset A = SetEq.valMultiset B :=
    (SetEq.prod_X_add_C_eq_iff A B).mp ((SetEq.mse_ldse_general hn₁ hn₂ A B).mpr hfrac)
  -- requests compress injectively outside event (2)
  have hAinj : Function.Injective A := by
    intro i₁ i₂ hi
    have hmem : ∀ i : Fin records.requests.length,
        records.requests.get i ∈ records.requests ++ records.responses :=
      fun i => List.mem_append_left _ (List.get_mem _ _)
    have hrec := rlc_inj_of_not_collision hγ (hmem i₁) (hmem i₂) hi
    exact List.nodup_iff_injective_get.mp hreqnd hrec
  have hAnd : (SetEq.valMultiset A).Nodup :=
    Multiset.Nodup.map hAinj Finset.univ.nodup
  have hBnd : (SetEq.valMultiset B).Nodup := hmulti ▸ hAnd
  have hBinj : Function.Injective B := by
    intro j₁ j₂ hj
    exact Multiset.inj_on_of_nodup_map hBnd j₁ (Finset.mem_univ j₁) j₂ (Finset.mem_univ j₂) hj
  rw [List.nodup_iff_injective_get]
  intro j₁ j₂ hj
  apply hBinj
  show Walk.rlc coins.gamma (records.responses.get j₁) =
    Walk.rlc coins.gamma (records.responses.get j₂)
  rw [hj]

end FiniteIO

namespace OptimizedHostileTimestamps

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open OptimizedComputeBaseGates
open OptimizedComputeFinal
open OptimizedComputeCorrectedFinal
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeFiniteIOGates
open OptimizedComputeSemanticRealization
open OptimizedComputeHostileAccumulator
open StrictExtension
open OptimizedComputeFinalTrace
open ConcreteStrictPackage
open TemplateRawJointSoundness
open Module
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F]
  [Field K] [Algebra F K] [FiniteDimensional F K]

/-- `ln_prev` of the row. -/
def lnPrevAt (env : CorrectedFinalTypedEnv F K) : K := env.extTrace 54

/-- `ln` of the row. -/
def lnCurAt (env : CorrectedFinalTypedEnv F K) : K := env.extTrace 55

/-- The timestamp base as the row reads it: compute challenge slot `0`. -/
def alphaAt (env : CorrectedFinalTypedEnv F K) : K := env.toSourceEnv.chal 0

theorem source_trace_lnPrev (env : CorrectedFinalTypedEnv F K) :
    env.toSourceEnv.trace 67 = lnPrevAt env := source_trace_ext env 54

theorem source_trace_lnCur (env : CorrectedFinalTypedEnv F K) :
    env.toSourceEnv.trace 68 = lnCurAt env := source_trace_ext env 55

omit [FiniteDimensional F K] in
theorem source_traceNext_ext (env : CorrectedFinalTypedEnv F K) (i : Fin 63) :
    env.toSourceEnv.traceNext (13 + (i : ℕ)) = env.extTraceNext i := by
  simp only [CorrectedFinalTypedEnv.toSourceEnv]
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 1
  apply Fin.ext
  simp

omit [FiniteDimensional F K] in
theorem source_trace_base (env : CorrectedFinalTypedEnv F K) (i : ℕ) (hi : i < 13) :
    env.toSourceEnv.trace i = algebraMap F K (env.baseTrace ⟨i, hi⟩) := by
  simp only [CorrectedFinalTypedEnv.toSourceEnv, dif_pos hi]

/-- **`mem_record₁`'s timestamp is `ln_prev·α`**, by construction of the
decoder: source column `74` is not committed, it is `computeTraceSubst 74 = ln_prev·α`. -/
theorem rowRecord_ts_zero (env : CorrectedFinalTypedEnv F K) :
    OptimizedComputeHostileAccumulator.rowRecord env 0 7 = lnPrevAt env * alphaAt env := by
  have h : computeTraceSubst .traceCur (67 + 8 * ((0 : Fin 3) : ℕ) + ((7 : Fin 10) : ℕ)) =
      .Mul (lnPrev .traceCur) (.Var .challenge 0) := subst_tc74
  unfold OptimizedComputeHostileAccumulator.rowRecord
  rw [if_neg (by decide : ¬ ((7 : Fin 10) : ℕ) = 9), if_neg (by decide : ¬ ((7 : Fin 10) : ℕ) = 6), if_neg (by decide : ¬ ((7 : Fin 10) : ℕ) = 8), h]
  simp only [Expr.subst, finalSampledNamespace, lnPrev, ext0, Expr.eval, alphaAt]
  rw [source_trace_lnPrev]

/-- **`mem_record₂`'s timestamp is `a₁·ln_prev·α²`** with `a₁` the
slot's selector-derived activity mask (`op₀ + Σ_{2,5,6,7,8,9} opₖ`), by construction
(`mr2Field 7`). -/
theorem rowRecord_ts_one (env : CorrectedFinalTypedEnv F K) :
    OptimizedComputeHostileAccumulator.rowRecord env 1 7 = activeMask env 1 *
        (lnPrevAt env * alphaAt env ^ 2) := by
  have h : computeTraceSubst .traceCur (67 + 8 * ((1 : Fin 3) : ℕ) + ((7 : Fin 10) : ℕ)) =
      .Mul (sampledActive .traceCur 1) (.Mul (lnPrev .traceCur) (.Pow (.Var .challenge 0) 2)) := by
    change computeTraceSubst .traceCur 82 = _
    norm_num [computeTraceSubst, mr2Field, mr2Group, sampledActive]
  unfold OptimizedComputeHostileAccumulator.rowRecord
  rw [if_neg (by decide : ¬ ((7 : Fin 10) : ℕ) = 9), if_neg (by decide : ¬ ((7 : Fin 10) : ℕ) = 6), if_neg (by decide : ¬ ((7 : Fin 10) : ℕ) = 8), h]
  simp only [Expr.subst, finalSampledNamespace, lnPrev, ext0, Expr.eval, alphaAt, activeMask,
    sampledActive, Fin.isValue, Fin.val_one]
  rw [source_trace_lnPrev]

/-- **`mem_record₃`'s timestamp is `a₂·ln_prev·α³`** with `a₂ = op₆ +
op₉`, by construction (`mr3Field 7`). -/
theorem rowRecord_ts_two (env : CorrectedFinalTypedEnv F K) :
    OptimizedComputeHostileAccumulator.rowRecord env 2 7 = activeMask env 2 *
        (lnPrevAt env * alphaAt env ^ 3) := by
  have h : computeTraceSubst .traceCur (67 + 8 * ((2 : Fin 3) : ℕ) + ((7 : Fin 10) : ℕ)) =
      .Mul (sampledActive .traceCur 2) (.Mul (lnPrev .traceCur) (.Pow (.Var .challenge 0) 3)) := by
    change computeTraceSubst .traceCur 90 = _
    norm_num [computeTraceSubst, mr3Field, mr3Group, sampledActive]
  unfold OptimizedComputeHostileAccumulator.rowRecord
  rw [if_neg (by decide : ¬ ((7 : Fin 10) : ℕ) = 9), if_neg (by decide : ¬ ((7 : Fin 10) : ℕ) = 6), if_neg (by decide : ¬ ((7 : Fin 10) : ℕ) = 8), h]
  simp only [Expr.subst, finalSampledNamespace, lnPrev, ext0, Expr.eval, alphaAt, activeMask,
    sampledActive, Fin.isValue, Fin.val_two]
  rw [source_trace_lnPrev]

/-- **The committed timestamp form, per active slot:** on any typed row,
the timestamp coordinate of an active request slot `j` is `ln_prev · α^{j+1}` — with no gate and
no hypothesis, because the optimized layout decodes it rather than committing it. -/
theorem rowRecord_ts_active (env : CorrectedFinalTypedEnv F K) (j : Fin 3)
    (hact : activeMask env j = 1) :
    rowRecord env j 7 = lnPrevAt env * alphaAt env ^ ((j : ℕ) + 1) := by
  fin_cases j
  · simp [rowRecord_ts_zero]
  · simp only [Fin.mk_one, Fin.isValue] at hact ⊢
    rw [rowRecord_ts_one, hact, one_mul]
  · simp only [Fin.reduceFinMk, Fin.isValue] at hact ⊢
    rw [rowRecord_ts_two, hact, one_mul]

/-- The number of memory records an opcode requests. -/
def arity : ComputeTable.State → ℕ
  | .s0 => 2 | .s1 => 1 | .s2 => 2 | .s3 => 1 | .s4 => 1
  | .s5 => 2 | .s6 => 3 | .s7 => 2 | .s8 => 2 | .s9 => 3 | .cons => 1

def lnAExpr : ℕ → Expr
  | 1 => lnA1 | 2 => lnA2 | _ => lnA3

/-- The opcode's committed `ln` recurrence gate, as it sits in the deployed source family. -/
def lnGate (s : ComputeTable.State) : Expr :=
  (gateBy s (.Sub (tc 66) (lnAExpr (arity s)))).subst computeSubst

set_option maxRecDepth 100000 in
/-- The recurrence gate is in the opcode's deployed per-state block (kernel-checked membership in
the deployed source list). -/
theorem lnGate_mem_stateBlock (s : ComputeTable.State) : lnGate s ∈ stateBlock s := by
  cases s <;> decide

/-- What the recurrence gate evaluates to on a source environment. -/
theorem lnGate_eval (s : ComputeTable.State) (E : Env K) :
    (lnGate s).eval E = E.trace (opCol s) * (E.trace 68 - E.trace 67 * E.chal 0 ^ arity s) := by
  unfold lnGate gateBy
  rw [Expr.eval_subst]
  cases s <;>
    simp [Env.ofSubst, computeSubst, computeTraceSubst, lnAExpr, lnA1, lnA2, lnA3, tc, chl,
      Expr.eval, lnCur, lnPrev, ext0, opCol, arity]

omit [FiniteDimensional F K] in
/-- Every packed row-local extension gate (`0..72`) vanishes unmasked on any row of an accepted
trace.  Cross-row slots `73..76` and the IO chain `80` are last-row-masked or residual. -/
theorem packed_unmasked_zero {n : ℕ} {env : CorrectedFinalTypedEnv F K} {envF : Env F}
    (hsource : CorrectedComputeSourceObligations n env envF)
    (i : CorrectedCoreExtGateId)
    (h75 : i ≠ packedWalkCountId) (h76 : i ≠ packedWalkAccId)
    (h80 : i ≠ packedChainId) (h89 : ¬ (i = packedLnChainId ∨ i = packedWalkLnId)) :
    (correctedFinalExtGate i).eval env = 0 := by
  have hc := hsource.extensionCore21 i
  simpa [correctedCoreSemanticValue, h75, h76, h80, h89] using hc

omit [FiniteDimensional F K] in
/-- The 73 row-local packed gates vanish at the source level on any accepted row (no `notLast`
hypothesis: they do not read a successor). -/
theorem paperPackingRowLocal_eval_zero {n : ℕ} {env : CorrectedFinalTypedEnv F K} {envF : Env F}
    (hsource : CorrectedComputeSourceObligations n env envF) :
    ∀ g ∈ paperPackingRowLocal, g.eval env.toSourceEnv = 0 := by
  intro g hg
  obtain ⟨k, hget⟩ := List.mem_iff_get.mp hg
  have hk : (k : ℕ) < 72 := by
    have := k.isLt
    simpa [paperPackingRowLocal_length] using this
  have hgate := packed_unmasked_zero hsource ⟨k.val, by omega⟩
    (by intro h; have := congrArg Fin.val h; simp [packedWalkCountId] at this; omega)
    (by intro h; have := congrArg Fin.val h; simp [packedWalkAccId] at this; omega)
    (by intro h; have := congrArg Fin.val h; simp [packedChainId] at this; omega)
    (by intro h; rcases h with h | h
        · have := congrArg Fin.val h; simp [packedLnChainId] at this; omega
        · have := congrArg Fin.val h; simp [packedWalkLnId] at this; omega)
  have hlen : (k : ℕ) < finalExtTransitionGates.length := by simp; omega
  have hsrc := (correctedFinalExtGate_eval_source env ⟨k.val, by omega⟩).trans hgate
  have hget' : finalExtTransitionGates.get ⟨k.val, hlen⟩ =
      paperPackingRowLocal.get k := by
    have hk' : k.val < paperPackingRowLocal.length := k.isLt
    have hdecomp : finalExtTransitionGates =
        paperPackingRowLocal ++ (crossRowSingletons ++
          OptimizedComputeGateBasis.queueWitnessGates ++ finalSampledIOTransitionGates) := by
      rw [finalExtTransitionGates, paperPacking_eq_rowLocal_append]
      simp [List.append_assoc]
    have hq : finalExtTransitionGates[k.val]? = paperPackingRowLocal[k.val]? := by
      rw [hdecomp]
      exact List.getElem?_append_left hk'
    apply Option.some_inj.mp
    simpa [List.get_eq_getElem] using
      (List.getElem?_eq_getElem hlen).symm.trans (hq.trans (List.getElem?_eq_getElem hk'))
  rw [← hget, ← hget']
  exact hsrc

omit [FiniteDimensional F K] in
/-- Every per-state atomic vanishes on an accepted row whose selector is the one-hot of `s`,
read off the packed table (`paperPacking_iff_atomic`) with no fold coin. -/
theorem stateBlock_sources_vanish {n : ℕ} {env : CorrectedFinalTypedEnv F K} {envF : Env F}
    (hsource : CorrectedComputeSourceObligations n env envF)
    (s : ComputeTable.State)
    (hsel : ∀ st, env.toSourceEnv.trace (opCol st) = ComputeTable.opSel s st)
    (hz : (zZinvExpr.subst computeSubst).eval env.toSourceEnv = 0) :
    ∀ e ∈ stateBlock s, e.eval env.toSourceEnv = 0 := by
  have hone : ComputePaperPacking.OneHotSelector env.toSourceEnv s := by
    intro st
    simpa [ComputeTable.opSel] using hsel st
  have hpk : ∀ g ∈ packedTableOptimized, g.eval env.toSourceEnv = 0 := fun g hg =>
    paperPackingRowLocal_eval_zero hsource g (List.mem_append.mpr (Or.inl hg))
  exact (ComputePaperPacking.paperPacking_iff_atomic env.toSourceEnv s hone hz).1 hpk s

/-- **The `ln` recurrence, hostilely.**  On a row of an accepted trace
whose selector is the one-hot of `s`, `ln = ln_prev · α^{arity s}` — read off the packed
`lnGate` with no fold-coin hypothesis. -/
theorem ln_recurrence {n : ℕ} {env : CorrectedFinalTypedEnv F K} {envF : Env F}
    (hsource : CorrectedComputeSourceObligations n env envF)
    (s : ComputeTable.State)
    (hsel : ∀ st, env.toSourceEnv.trace (opCol st) = ComputeTable.opSel s st)
    (hz : (zZinvExpr.subst computeSubst).eval env.toSourceEnv = 0) :
    lnCurAt env = lnPrevAt env * alphaAt env ^ arity s := by
  have h := stateBlock_sources_vanish hsource s hsel hz (lnGate s) (lnGate_mem_stateBlock s)
  rw [lnGate_eval, hsel s, source_trace_lnCur, source_trace_lnPrev] at h
  simp only [ComputeTable.opSel, if_true, one_mul, sub_eq_zero] at h
  exact h

/-- Typed form of `isFirst · (ln_prev − 1)`. -/
def lnInitTyped : CorrectedFinalTypedExpr := (correctedLowerFinal finalLnInit).getD (.const 0)

theorem lower_lnInit : correctedLowerFinal finalLnInit = some lnInitTyped := by decide

/-- The origin gate is a member of the committed degree-two endpoint bucket. -/
theorem lnInit_mem_endpoint2 : lnInitTyped ∈ correctedEndpoint2 := by
  rw [correctedEndpoint2, List.mem_filterMap]
  exact ⟨finalLnInit, by simp, lower_lnInit⟩

/-- What the origin gate says on any typed environment: `isFirst · (ln_prev − 1)`. -/
theorem lnInit_eval (env : CorrectedFinalTypedEnv F K) :
    lnInitTyped.eval env = algebraMap F K (env.baseTrace 11) * (lnPrevAt env - 1) := by
  rw [← correctedLowerFinal_eval env _ _ lower_lnInit]
  simp [finalLnInit, OptimizedComputeTemplate.fixedIsFirst, lnPrev, ext0, Expr.eval,
    lnPrevAt, CorrectedFinalTypedEnv.toSourceEnv]

theorem finalExtTransitionGates_get_lnChain :
    finalExtTransitionGates.get ⟨packedLnChainIdx, by simp [packedLnChainIdx]⟩ =
      Trans.lnChainExpr.subst computeSubst := by
  simp [finalExtTransitionGates, paperPackingNonIOGates, paperPacking_eq_rowLocal_append,
    packedLnChainIdx, packedLnChainId, paperPackingRowLocal_length, crossRowSingletons,
    List.getElem_append_right, List.append_assoc]

/-- **The hand-off, hostilely.**  Off the last row, `ln(i) = ln_prev(i+1)` (read from the
next-row column). -/
theorem ln_chain {n : ℕ} {env : CorrectedFinalTypedEnv F K} {envF : Env F}
    (hsource : CorrectedComputeSourceObligations n env envF)
    (hnotLast : env.baseTrace 12 = 0) :
    lnCurAt env = env.extTraceNext 54 := by
  have hc := hsource.extensionCore21 packedLnChainId
  have h75 : packedLnChainId ≠ packedWalkCountId := by decide
  have h76 : packedLnChainId ≠ packedWalkAccId := by decide
  have h80 : packedLnChainId ≠ packedChainId := by decide
  have h89 : packedLnChainId = packedLnChainId ∨ packedLnChainId = packedWalkLnId := Or.inl rfl
  have hgate : (correctedFinalExtGate packedLnChainId).eval env = 0 := by
    simp only [correctedCoreSemanticValue, h75, h76, h80, h89, ↓reduceIte, notLastScalar,
      hnotLast, map_one, sub_zero, one_mul] at hc
    exact hc
  have h2 : (finalExtTransitionGates.get ⟨packedLnChainIdx, by simp [packedLnChainIdx]⟩).eval
      env.toSourceEnv = 0 :=
    (correctedFinalExtGate_eval_source env packedLnChainId).trans hgate
  rw [finalExtTransitionGates_get_lnChain] at h2
  have hE : (Trans.lnChainExpr.subst computeSubst).eval env.toSourceEnv =
      env.toSourceEnv.trace 68 - env.toSourceEnv.traceNext 67 := by
    simp [Trans.lnChainExpr, Trans.tn, Expr.subst, Expr.eval, computeSubst,
      computeTraceSubst, lnCur, lnPrev, ext0, tc]
  rw [hE, source_trace_lnCur, sub_eq_zero] at h2
  rw [h2]
  exact source_traceNext_ext env 54

section Arity

variable [DecidableEq K]

/-- The number of active request slots of a row, read off the selector-derived masks: `3` if slot `2` is active, else `2` if slot `1` is, else `1`. -/
def rowArity (env : CorrectedFinalTypedEnv F K) : ℕ :=
  if activeMask env 2 = 1 then 3 else if activeMask env 1 = 1 then 2 else 1

omit [FiniteDimensional F K] in
theorem rowArity_le (env : CorrectedFinalTypedEnv F K) : rowArity env ≤ 3 := by
  unfold rowArity; split_ifs <;> omega

omit [FiniteDimensional F K] in
/-- An active slot's index is below the row's arity. -/
theorem active_lt_rowArity (env : CorrectedFinalTypedEnv F K) (j : Fin 3)
    (hact : activeMask env j = 1) : (j : ℕ) + 1 ≤ rowArity env := by
  unfold rowArity
  have hj := j.isLt
  have hne : ∀ k : Fin 3, activeMask env k ≠ 1 → (j : ℕ) ≠ (k : ℕ) := by
    intro k hk hjk
    exact hk (by rw [show k = j from Fin.ext hjk.symm]; exact hact)
  by_cases h2 : activeMask env 2 = 1
  · rw [if_pos h2]; omega
  · rw [if_neg h2]
    have h2' := hne 2 h2
    by_cases h1 : activeMask env 1 = 1
    · rw [if_pos h1]
      simp only [Fin.val_two] at h2'
      omega
    · rw [if_neg h1]
      have h1' := hne 1 h1
      simp only [Fin.val_two] at h2'
      simp only [Fin.val_one] at h1'
      omega

omit [FiniteDimensional F K] [DecidableEq K] in
/-- `activeMask env 0 = 1` always (`sampledActive 0 = 1`). -/
theorem activeMask_zero (env : CorrectedFinalTypedEnv F K) : activeMask env 0 = 1 := by
  simp [activeMask, sampledActive, Expr.eval]

end Arity

end

end OptimizedHostileTimestamps

end Nock.NockVMROM.Thm54
