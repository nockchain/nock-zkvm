/-
  Nock/NockVMROM/Thm54/P8Core/SVIOCompute.lean

  **The compute half of the IO twins,
  package-free.**

  `FamilyIOChainCompute` derives the LogUp request identity of an accepted family compute trace
  from the package `P` (rows, nodes, basis, orbit and the package `requests` public).  This module re-derives the same chain once, over an abstract
  row family `IORows` that carries only what the chain reads, and instantiates it at the
  un-hosted compute chip `Unhosted309.computeChipAt309` with **arbitrary** nodes, basis, orbit and
  public map:

  * `IORowObligations` — the IO-relevant sub-bundle of the row obligations (base gates, every
    packed core gate except the two retargeted queue gates, the anchored step `aux[2]`, and the
    three untouched endpoints `accInit` / `accTerminal` / `lnInit`).  It is exactly what both the
    deployed 303 decomposition and the 309 decomposition (`SourceObligations309`) give, so the
    chain below is chip-agnostic (`IORowObligations.of309`).
  * `IORows` — a row family with those obligations, the first/last masks, orbit alignment of the
    extension roles and a row-constant challenge map `κ`.
  * The chain: `requests_eq_sum_compress` (the terminal public is the LogUp sum of the committed
    request records at the coins `⟨κ 7, κ 8⟩`), `requests_nodup` (from the committed timestamps
    outside `TimestampCollisionEvent` at `κ 0`), and the pole exclusion helpers.
  * `rows309` — the instance at `computeChipAt309 hn nodes b pubVal orbit c` (any `c`, any
    `pubVal`), with `κ = computeKOfTuple c` and the terminal public read off `pubVal 6..8`.

  Paper: the paper (the compute accumulator and its terminal), `:597-599` (the shared
  `requests`), `:603-609` (unique requests), `:1852-1887` (the timestamp line).
-/
import Nock.NockVMROM.Thm54.Unhosted309Realization
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.FamilyIOChainCompute
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.OptimizedHostileTimestamps

namespace Nock.NockVMROM.Thm54.SVIO

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open OptimizedStrictPackage
open OptimizedComputeBaseGates
open OptimizedComputeFinal
open OptimizedComputeCorrectedFinal
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeSemanticRealization
open OptimizedComputeFiniteIOGates
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open DeployedChipFamily
open Unhosted309
open StrictExtension
open Module
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-! ## 1. The IO-relevant row obligations -/

/-- **The IO-relevant sub-bundle of the compute row obligations.**  Every field is a committed
gate of both the deployed 303 chip and the un-hosted 309 chip at the same gathered environment:
the base gates, every packed core gate except the two retargeted queue gates, the anchored
accumulator step (`aux[2]`), and the three untouched degree-two endpoints. -/
structure IORowObligations (n : ℕ) (env : CorrectedFinalTypedEnv F K) (envF : Env F) : Prop where
  base15 : ∀ g ∈ finalBaseTransitionGates n, g.eval envF = 0
  base_eq : ∀ (k : ℕ) (hk : k < 13), env.baseTrace ⟨k, hk⟩ = envF.trace k
  core : ∀ i : CorrectedCoreExtGateId, i ≠ packedQueueNonEmptyId → i ≠ packedQueueTilingId →
    correctedCoreSemanticValue env i = 0
  aux2 : correctedAccAfterStep.eval env = 0
  accInit : accInitTyped.eval env = 0
  accTerminal : accTerminalTyped.eval env = 0
  lnInit : lnInitTyped.eval env = 0

/-- The deployed 303 decomposition gives the IO sub-bundle (positive control: the sub-bundle is
no stronger than what the deployed chain already used). -/
theorem IORowObligations.of303 {n : ℕ} {b : Basis (Fin 3) F K} {envF : Env F}
    (h : CorrectedComputeSourceObligations n (gatherCorrectedFinalTypedEnv b envF) envF) :
    IORowObligations n (gatherCorrectedFinalTypedEnv b envF) envF where
  base15 := h.base15
  base_eq := fun _ _ => rfl
  core := fun i _ _ => h.extensionCore21 i
  aux2 := by simpa [correctedAuxSemanticValue] using h.residualAux3 2
  accInit := h.endpointDegreeTwo2 _ anchors_mem_endpoint2.1
  accTerminal := h.endpointDegreeTwo2 _ anchors_mem_endpoint2.2
  lnInit := h.endpointDegreeTwo2 _ lnInit_mem_endpoint2

theorem accInit_mem_endpoint2_309 : lowerLeaf finalAccInit ∈ endpoint2_309 := by
  simp [endpoint2_309]

theorem accTerminal_mem_endpoint2_309 : lowerLeaf finalAccTerminal ∈ endpoint2_309 := by
  simp [endpoint2_309]

theorem lnInit_mem_endpoint2_309 : lowerLeaf finalLnInit ∈ endpoint2_309 := by
  simp [endpoint2_309]

/-- **The un-hosted 309 decomposition gives the IO sub-bundle** at the deployed gathered
environment `(gather309 b envF).base`.  The two queue positions are the only retargeted core
gates; `aux[2]` and the three IO / origin endpoints are untouched. -/
theorem IORowObligations.of309 {n : ℕ} {b : Basis (Fin 3) F K} {envF : Env F}
    (h : SourceObligations309 n (gather309 b envF) envF) :
    IORowObligations n (gatherCorrectedFinalTypedEnv b envF) envF where
  base15 := h.base15
  base_eq := fun _ _ => rfl
  core := fun i h1 h2 => by
    have hc := h.extensionCore i
    simp only [coreSemValue309, h1, h2, ↓reduceIte] at hc
    exact hc
  aux2 := by
    have ha := h.residualAux 2
    simp only [auxSemValue309, ↓reduceDIte, correctedAuxSemanticValue, ↓reduceIte] at ha
    exact ha
  accInit := h.endpointDegreeTwo _ accInit_mem_endpoint2_309
  accTerminal := h.endpointDegreeTwo _ accTerminal_mem_endpoint2_309
  lnInit := h.endpointDegreeTwo _ lnInit_mem_endpoint2_309

/-! ## 2. The row-local readers, at the sub-bundle -/

section Readers

variable {n : ℕ} {env : CorrectedFinalTypedEnv F K} {envF : Env F}

/-- Twin of `packed_unmasked_zero` at the sub-bundle. -/
theorem packed_unmasked_zero_io (hsource : IORowObligations n env envF)
    (i : CorrectedCoreExtGateId)
    (h75 : i ≠ packedWalkCountId) (h76 : i ≠ packedWalkAccId)
    (h80 : i ≠ packedChainId) (h89 : ¬ (i = packedLnChainId ∨ i = packedWalkLnId))
    (hq1 : i ≠ packedQueueNonEmptyId) (hq2 : i ≠ packedQueueTilingId) :
    (correctedFinalExtGate i).eval env = 0 := by
  have hc := hsource.core i hq1 hq2
  simpa [correctedCoreSemanticValue, h75, h76, h80, h89] using hc

/-- Twin of `paperPackingRowLocal_eval_zero` at the sub-bundle (the 72 row-local gates sit
below every special position). -/
theorem paperPackingRowLocal_eval_zero_io (hsource : IORowObligations n env envF) :
    ∀ g ∈ paperPackingRowLocal, g.eval env.toSourceEnv = 0 := by
  intro g hg
  obtain ⟨k, hget⟩ := List.mem_iff_get.mp hg
  have hk : (k : ℕ) < 72 := by
    have := k.isLt
    simpa [paperPackingRowLocal_length] using this
  have hgate := packed_unmasked_zero_io hsource ⟨k.val, by omega⟩
    (by intro h; have := congrArg Fin.val h; simp at this; omega)
    (by intro h; have := congrArg Fin.val h; simp at this; omega)
    (by intro h; have := congrArg Fin.val h; simp at this; omega)
    (by intro h; rcases h with h | h
        · have := congrArg Fin.val h; simp at this; omega
        · have := congrArg Fin.val h; simp at this; omega)
    (by intro h; have := congrArg Fin.val h; simp at this; omega)
    (by intro h; have := congrArg Fin.val h; simp at this; omega)
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

/-- Twin of `ln_recurrence` at the sub-bundle. -/
theorem ln_recurrence_io (hsource : IORowObligations n env envF)
    (s : ComputeTable.State)
    (hsel : ∀ st, env.toSourceEnv.trace (opCol st) = ComputeTable.opSel s st)
    (hz : (zZinvExpr.subst computeSubst).eval env.toSourceEnv = 0) :
    lnCurAt env = lnPrevAt env * alphaAt env ^ arity s := by
  have hone : ComputePaperPacking.OneHotSelector env.toSourceEnv s := by
    intro st
    simpa [ComputeTable.opSel] using hsel st
  have hpk : ∀ g ∈ packedTableOptimized, g.eval env.toSourceEnv = 0 := fun g hg =>
    paperPackingRowLocal_eval_zero_io hsource g (List.mem_append.mpr (Or.inl hg))
  have h := (ComputePaperPacking.paperPacking_iff_atomic env.toSourceEnv s hone hz).1 hpk s
    (lnGate s) (lnGate_mem_stateBlock s)
  rw [lnGate_eval, hsel s, source_trace_lnCur, source_trace_lnPrev] at h
  simp only [ComputeTable.opSel, if_true, one_mul, sub_eq_zero] at h
  exact h

/-- Twin of `ln_chain` at the sub-bundle. -/
theorem ln_chain_io (hsource : IORowObligations n env envF)
    (hnotLast : env.baseTrace 12 = 0) :
    lnCurAt env = env.extTraceNext 54 := by
  have hc := hsource.core packedLnChainId (by decide) (by decide)
  have h75 : packedLnChainId ≠ packedWalkCountId := by decide
  have h76 : packedLnChainId ≠ packedWalkAccId := by decide
  have h80 : packedLnChainId ≠ packedChainId := by decide
  have hgate : (correctedFinalExtGate packedLnChainId).eval env = 0 := by
    simp only [correctedCoreSemanticValue, h75, h76, h80, ↓reduceIte, notLastScalar,
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

end Readers

/-! ## 3. An abstract accepted compute row family -/

/-- **An accepted compute row family**, chip-agnostic: `n` rows of gathered environments with the
IO sub-bundle, the first/last-row masks, orbit alignment of the extension roles, and a
row-constant challenge map `κ` (slots `0..11`). -/
structure IORows (F K : Type) [Field F] [Field K] [Algebra F K] where
  n : ℕ
  hn : 0 < n
  env : Fin n → CorrectedFinalTypedEnv F K
  envF : Fin n → Env F
  obl : ∀ i, IORowObligations n (env i) (envF i)
  first : ∀ i, (env i).baseTrace 11 = if (i : ℕ) = 0 then 1 else 0
  last : ∀ i, (env i).baseTrace 12 = if (i : ℕ) + 1 = n then 1 else 0
  next : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n) (r : Fin 63),
    (env i).extTraceNext r = (env ⟨(i : ℕ) + 1, hi⟩).extTrace r
  κ : ℕ → K
  chal : ∀ (i : Fin n) (q : ℕ), q < 12 → (env i).toSourceEnv.chal q = κ q

namespace IORows

variable (R : IORows F K)

abbrev firstRow : Fin R.n := ⟨0, R.hn⟩
abbrev lastRow : Fin R.n := ⟨R.n - 1, Nat.sub_lt R.hn (by omega)⟩

/-- The IO coins every row reads (`γ` = slot `7`, pole = slot `8`). -/
abbrev coins : FiniteIO.IOCoins K := ⟨R.κ 7, R.κ 8⟩

theorem rowCoins_eq (i : Fin R.n) : rowCoins (R.env i) = R.coins := by
  simp only [rowCoins, R.chal i 7 (by norm_num), R.chal i 8 (by norm_num)]

theorem alphaAt_eq (i : Fin R.n) : alphaAt (R.env i) = R.κ 0 := R.chal i 0 (by norm_num)

theorem not_last (i : Fin R.n) (hi : (i : ℕ) + 1 < R.n) : (R.env i).baseTrace 12 = 0 := by
  rw [R.last i, if_neg (by omega)]

theorem acc_first : (R.env R.firstRow).extTrace 32 = 0 := by
  have hgate := (R.obl R.firstRow).accInit
  rw [accInit_eval, R.first, if_pos rfl] at hgate
  simpa using hgate

theorem accAfter_last : (R.env R.lastRow).extTrace 60 = (R.env R.lastRow).extensionPublic 2 := by
  have hgate := (R.obl R.lastRow).accTerminal
  have hl : ((R.lastRow : ℕ) + 1 = R.n) := Nat.sub_add_cancel R.hn
  rw [accTerminal_eval, R.last, if_pos hl] at hgate
  simpa [sub_eq_zero] using hgate

theorem chain (i : Fin R.n) (hi : (i : ℕ) + 1 < R.n) :
    (R.env i).extTrace 60 = (R.env i).extTraceNext 32 := by
  have h := (R.obl i).core packedChainId (by decide) (by decide)
  have hnl := R.not_last i hi
  simp only [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId, packedChainId,
    ↓reduceIte] at h
  simpa [accAfterChain, CorrectedFinalTypedExpr.eval, hnl, sub_eq_zero] using h

/-- The running sum, as in `prefixSumAt`. -/
def prefixSum (m : ℕ) : K :=
  ∑ k ∈ Finset.range m, if h : k < R.n then rowTerm (R.env ⟨k, h⟩) else 0

theorem prefixSum_succ (m : ℕ) (hm : m < R.n) :
    R.prefixSum (m + 1) = R.prefixSum m + rowTerm (R.env ⟨m, hm⟩) := by
  simp [prefixSum, Finset.sum_range_succ, hm]

theorem acc_eq_prefixSum
    (hden : ∀ (i : Fin R.n) (j : Fin 3), safeDenomWitness (R.env i) j ≠ 0) :
    ∀ (m : ℕ) (hm : m < R.n), (R.env ⟨m, hm⟩).extTrace 32 = R.prefixSum m := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp only [prefixSum, Finset.range_zero, Finset.sum_empty]
      exact R.acc_first
  | succ m ih =>
      intro hm
      have hm' : m < R.n := by omega
      rw [← R.next ⟨m, hm'⟩ hm 32, ← R.chain ⟨m, hm'⟩ hm,
        accAfter_eq_of_step _ (R.obl ⟨m, hm'⟩).aux2 (hden _), ih hm', R.prefixSum_succ m hm']

theorem requests_eq_sum_rowTerms
    (hden : ∀ (i : Fin R.n) (j : Fin 3), safeDenomWitness (R.env i) j ≠ 0) :
    (R.env R.lastRow).extensionPublic 2 = ∑ i : Fin R.n, rowTerm (R.env i) := by
  have hlast : (R.env R.lastRow).extTrace 32 = R.prefixSum (R.n - 1) :=
    R.acc_eq_prefixSum hden (R.n - 1) _
  have hstep := accAfter_eq_of_step _ (R.obl R.lastRow).aux2 (hden _)
  rw [← R.accAfter_last, hstep, hlast, ← R.prefixSum_succ (R.n - 1) _, Nat.sub_add_cancel R.hn]
  simp only [prefixSum]
  rw [← Fin.sum_univ_eq_sum_range (fun k => if h : k < R.n then
    rowTerm (R.env ⟨k, h⟩) else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [i.isLt]

theorem denomPin (i : Fin R.n) (j : Fin 3) :
    safeDenomWitness (R.env i) j =
      SafeDenom (activeMask (R.env i) j) (slotDenominator (R.env i) j) := by
  have hne : ∀ q : CorrectedCoreExtGateId, q = ⟨78 + (j : ℕ), by have := j.isLt; omega⟩ →
      q ≠ packedWalkCountId ∧ q ≠ packedWalkAccId ∧ q ≠ packedChainId ∧
        ¬ (q = packedLnChainId ∨ q = packedWalkLnId) ∧
        q ≠ packedQueueNonEmptyId ∧ q ≠ packedQueueTilingId := by
    rintro q rfl
    fin_cases j <;> decide
  obtain ⟨h10, h11, h20, h89, hq1, hq2⟩ := hne _ rfl
  have h := (R.obl i).core ⟨78 + (j : ℕ), by have := j.isLt; omega⟩ hq1 hq2
  simp only [correctedCoreSemanticValue, h10, h11, h20, h89, ↓reduceIte] at h
  exact (denomPin_eval_iff _ j).1 h

theorem rowTerm_eq_logUp (i : Fin R.n)
    (hbool : ∀ j : Fin 3, activeMask (R.env i) j = 0 ∨ activeMask (R.env i) j = 1) :
    rowTerm (R.env i) = logUpRowTerm (R.env i) := by
  simp only [rowTerm, logUpRowTerm, R.denomPin i,
    active_mul_safeDenom_inv _ _ (hbool 0), active_mul_safeDenom_inv _ _ (hbool 1),
    active_mul_safeDenom_inv _ _ (hbool 2)]

theorem requests_eq_sum_logUp
    (hbool : ∀ (i : Fin R.n) (j : Fin 3), activeMask (R.env i) j = 0 ∨ activeMask (R.env i) j = 1)
    (hpole : ∀ (i : Fin R.n) (j : Fin 3),
      activeMask (R.env i) j = 1 → slotDenominator (R.env i) j ≠ 0) :
    (R.env R.lastRow).extensionPublic 2 = ∑ i : Fin R.n, logUpRowTerm (R.env i) := by
  have hden : ∀ (i : Fin R.n) (j : Fin 3), safeDenomWitness (R.env i) j ≠ 0 := by
    intro i j
    rw [R.denomPin i j]
    exact safeDenom_ne_zero _ _ (hbool i j) (hpole i j)
  rw [R.requests_eq_sum_rowTerms hden]
  exact Finset.sum_congr rfl fun i _ => R.rowTerm_eq_logUp i (hbool i)

theorem selector_gates (i : Fin R.n) :
    (∀ (k : ℕ) (hk : k < 11),
      (R.env i).baseTrace ⟨k, by omega⟩ = 0 ∨ (R.env i).baseTrace ⟨k, by omega⟩ = 1) ∧
    ((R.env i).baseTrace ⟨0, by norm_num⟩ + (R.env i).baseTrace ⟨1, by norm_num⟩ +
      (R.env i).baseTrace ⟨2, by norm_num⟩ + (R.env i).baseTrace ⟨3, by norm_num⟩ +
      (R.env i).baseTrace ⟨4, by norm_num⟩ + (R.env i).baseTrace ⟨5, by norm_num⟩ +
      (R.env i).baseTrace ⟨6, by norm_num⟩ + (R.env i).baseTrace ⟨7, by norm_num⟩ +
      (R.env i).baseTrace ⟨8, by norm_num⟩ + (R.env i).baseTrace ⟨9, by norm_num⟩ +
      (R.env i).baseTrace ⟨10, by norm_num⟩) = 1 := by
  have hb := (R.obl i).base15
  have hbase := (R.obl i).base_eq
  constructor
  · intro k hk
    have hg := hb (selectorBool k) (by
      simp only [finalBaseTransitionGates, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl ⟨k, hk, rfl⟩)
    rw [hbase k (by omega)]
    simp only [selectorBool, bv, CoeffExpr.eval, mul_eq_zero, sub_eq_zero] at hg
    rcases hg with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  · have hg := hb selectorOneHot (by simp [finalBaseTransitionGates])
    simp [selectorOneHot, selectorSum, CoeffExpr.sumList, List.range_succ, bv, CoeffExpr.eval,
      sub_eq_zero] at hg
    simp only [hbase _ (by norm_num : (0 : ℕ) < 13), hbase _ (by norm_num : (1 : ℕ) < 13),
      hbase _ (by norm_num : (2 : ℕ) < 13), hbase _ (by norm_num : (3 : ℕ) < 13),
      hbase _ (by norm_num : (4 : ℕ) < 13), hbase _ (by norm_num : (5 : ℕ) < 13),
      hbase _ (by norm_num : (6 : ℕ) < 13), hbase _ (by norm_num : (7 : ℕ) < 13),
      hbase _ (by norm_num : (8 : ℕ) < 13), hbase _ (by norm_num : (9 : ℕ) < 13),
      hbase _ (by norm_num : (10 : ℕ) < 13)]
    linear_combination hg

variable [DecidableEq K]

theorem rowSelector_oneHot (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (i : Fin R.n) :
    ∃ s, rowSelector (R.env i) = Nock.ComputeTable.opSel s := by
  obtain ⟨hbool, hsum⟩ := R.selector_gates i
  apply Nock.ComputeTable.oneHot_of_bool_sum _ hchar
  · intro st
    rcases hbool (Nock.Reified.opCol st) (by cases st <;> decide) with h | h
    · left; simp [rowSelector, h]
    · right; simp [rowSelector, h]
  · have hK := congrArg (algebraMap F K) hsum
    simp only [map_add, map_one] at hK
    simp only [rowSelector, Nock.ComputeTable.sum09, Nock.Reified.opCol]
    linear_combination hK

theorem activeMask_bool (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (i : Fin R.n) (j : Fin 3) :
    activeMask (R.env i) j = 0 ∨ activeMask (R.env i) j = 1 := by
  obtain ⟨s, hs⟩ := R.rowSelector_oneHot hchar i
  have hv : ∀ st, algebraMap F K ((R.env i).baseTrace
      ⟨Nock.Reified.opCol st, by cases st <;> decide⟩) = Nock.ComputeTable.opSel s st :=
    fun st => congrFun hs st
  have h0 := hv .s0; have h2 := hv .s2; have h5 := hv .s5; have h6 := hv .s6
  have h7 := hv .s7; have h8 := hv .s8; have h9 := hv .s9
  simp only [Nock.Reified.opCol] at h0 h2 h5 h6 h7 h8 h9
  fin_cases j
  · right
    simp [activeMask, sampledActive, Expr.eval]
  · simp only [activeMask, sampledActive, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
      Fin.isValue]
    simp only [show (0 : ℕ) < 13 by norm_num, show (2 : ℕ) < 13 by norm_num,
      show (5 : ℕ) < 13 by norm_num, show (6 : ℕ) < 13 by norm_num,
      show (7 : ℕ) < 13 by norm_num, show (8 : ℕ) < 13 by norm_num,
      show (9 : ℕ) < 13 by norm_num, dite_true]
    rw [h0, h2, h5, h6, h7, h8, h9]
    cases s <;> simp [Nock.ComputeTable.opSel]
  · simp only [activeMask, sampledActive, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
      Fin.isValue]
    simp only [show (6 : ℕ) < 13 by norm_num, show (9 : ℕ) < 13 by norm_num, dite_true]
    rw [h6, h9]
    cases s <;> simp [Nock.ComputeTable.opSel]

theorem logUpRowTerm_eq_rowRequests (i : Fin R.n)
    (hbool : ∀ j : Fin 3, activeMask (R.env i) j = 0 ∨ activeMask (R.env i) j = 1) :
    logUpRowTerm (R.env i) =
      ((rowRequests (R.env i)).map fun r => (FiniteIO.compress R.coins r)⁻¹).sum := by
  have hterm : ∀ j : Fin 3,
      activeMask (R.env i) j * (slotDenominator (R.env i) j)⁻¹ =
      if activeMask (R.env i) j = 1
        then (FiniteIO.compress R.coins (rowRecord (R.env i) j))⁻¹
        else 0 := by
    intro j
    rw [slotDenominator_eq_compress, R.rowCoins_eq]
    rcases hbool j with h | h <;> simp [h]
  simp only [logUpRowTerm, hterm 0, hterm 1, hterm 2, rowRequests, List.finRange,
    List.ofFn_succ, List.ofFn_zero, List.filterMap_cons, List.filterMap_nil,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  split_ifs <;> simp [add_assoc]

/-- **The committed request list**: every row's active-slot records, in row order. -/
def requests : List (Fin 10 → K) :=
  (List.ofFn fun i : Fin R.n => rowRequests (R.env i)).flatten

theorem mem_requests {r : Fin 10 → K} (hr : r ∈ R.requests) :
    ∃ (i : Fin R.n) (j : Fin 3), activeMask (R.env i) j = 1 ∧ r = rowRecord (R.env i) j := by
  simp only [requests, List.mem_flatten, List.mem_ofFn] at hr
  obtain ⟨l, ⟨i, rfl⟩, hl⟩ := hr
  simp only [rowRequests, List.mem_filterMap, List.mem_finRange, true_and] at hl
  obtain ⟨j, hj⟩ := hl
  by_cases hact : activeMask (R.env i) j = 1
  · rw [if_pos hact] at hj
    exact ⟨i, j, hact, (Option.some_inj.mp hj).symm⟩
  · rw [if_neg hact] at hj
    exact absurd hj (by simp)

theorem rowRecord_mem_requests (i : Fin R.n) (j : Fin 3) (hact : activeMask (R.env i) j = 1) :
    rowRecord (R.env i) j ∈ R.requests := by
  simp only [requests, List.mem_flatten, List.mem_ofFn]
  refine ⟨_, ⟨i, rfl⟩, ?_⟩
  simp only [rowRequests, List.mem_filterMap, List.mem_finRange, true_and]
  exact ⟨j, by rw [if_pos hact]⟩

/-- **The compute LogUp identity, package-free.**  Under boolean masks and the compute-side pole
exclusion, the terminal public of the last row is the LogUp sum of the committed request
records at the row coins. -/
theorem requests_eq_sum_compress
    (hbool : ∀ (i : Fin R.n) (j : Fin 3), activeMask (R.env i) j = 0 ∨ activeMask (R.env i) j = 1)
    (hpole : ∀ (i : Fin R.n) (j : Fin 3),
      activeMask (R.env i) j = 1 → slotDenominator (R.env i) j ≠ 0) :
    (R.env R.lastRow).extensionPublic 2 =
      (R.requests.map fun r => (FiniteIO.compress R.coins r)⁻¹).sum := by
  rw [R.requests_eq_sum_logUp hbool hpole, requests, List.map_flatten, List.sum_flatten,
    List.map_map, List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [R.logUpRowTerm_eq_rowRequests i (hbool i)]
  rfl

/-- Pole exclusion from a hit-free pole on any record list containing the committed requests. -/
theorem pole_excluded_of_not_hit (rs : List (Fin 10 → K))
    (hhit : ∀ r ∈ R.requests ++ rs, FiniteIO.compress R.coins r ≠ 0) :
    ∀ (i : Fin R.n) (j : Fin 3),
      activeMask (R.env i) j = 1 → slotDenominator (R.env i) j ≠ 0 := by
  intro i j hact
  rw [slotDenominator_eq_compress, R.rowCoins_eq]
  exact hhit _ (List.mem_append_left _ (R.rowRecord_mem_requests i j hact))

/-! ### Timestamps and unique requests -/

theorem source_selector (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (i : Fin R.n) :
    ∃ s, ∀ st, (R.env i).toSourceEnv.trace (opCol st) = ComputeTable.opSel s st := by
  obtain ⟨s, hs⟩ := R.rowSelector_oneHot hchar i
  refine ⟨s, fun st => ?_⟩
  rw [source_trace_base _ (opCol st) (by cases st <;> decide)]
  exact congrFun hs st

theorem rowArity_eq_arity (i : Fin R.n) (s : ComputeTable.State)
    (hsel : ∀ st, (R.env i).toSourceEnv.trace (opCol st) = ComputeTable.opSel s st) :
    rowArity (R.env i) = arity s := by
  have h0 := hsel .s0; have h2 := hsel .s2; have h5 := hsel .s5; have h6 := hsel .s6
  have h7 := hsel .s7; have h8 := hsel .s8; have h9 := hsel .s9
  simp only [opCol] at h0 h2 h5 h6 h7 h8 h9
  unfold rowArity
  simp only [activeMask, sampledActive, Expr.eval, Fin.isValue, Fin.val_one, Fin.val_two, h0, h2,
    h5, h6, h7, h8, h9]
  cases s <;> simp [ComputeTable.opSel, arity]

theorem zZinv (i : Fin R.n) (hz : R.κ 1 ≠ 0) (h5 : R.κ 5 = (R.κ 1)⁻¹) :
    (zZinvExpr.subst computeSubst).eval (R.env i).toSourceEnv = 0 := by
  have h1 := R.chal i 1 (by norm_num)
  have h5' := R.chal i 5 (by norm_num)
  simp [zZinvExpr, Expr.subst, computeSubst, computeTraceSubst, chl, tc, Expr.eval, h1, h5', h5]
  exact sub_eq_zero.mpr (mul_inv_cancel₀ hz)

theorem ln_recurrence (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz : R.κ 1 ≠ 0) (h5 : R.κ 5 = (R.κ 1)⁻¹) (i : Fin R.n) :
    lnCurAt (R.env i) = lnPrevAt (R.env i) * R.κ 0 ^ rowArity (R.env i) := by
  obtain ⟨s, hsel⟩ := R.source_selector hchar i
  have h := ln_recurrence_io (R.obl i) s hsel (R.zZinv i hz h5)
  rw [R.alphaAt_eq] at h
  rw [R.rowArity_eq_arity i s hsel]
  exact h

theorem ln_chain (i : Fin R.n) (hi : (i : ℕ) + 1 < R.n) :
    lnCurAt (R.env i) = lnPrevAt (R.env ⟨(i : ℕ) + 1, hi⟩) := by
  rw [ln_chain_io (R.obl i) (R.not_last i hi)]
  exact R.next i hi 54

def prefixExp (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range m, if h : k < R.n then rowArity (R.env ⟨k, h⟩) else 0

theorem prefixExp_succ (m : ℕ) (hm : m < R.n) :
    R.prefixExp (m + 1) = R.prefixExp m + rowArity (R.env ⟨m, hm⟩) := by
  simp [prefixExp, Finset.sum_range_succ, hm]

theorem prefixExp_mono {a b : ℕ} (hab : a ≤ b) : R.prefixExp a ≤ R.prefixExp b := by
  unfold prefixExp
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) (fun _ _ _ => Nat.zero_le _)

def ln0 : K := lnPrevAt (R.env R.firstRow)

theorem ln0_eq_one : R.ln0 = 1 := by
  have hgate := (R.obl R.firstRow).lnInit
  rw [lnInit_eval, R.first] at hgate
  simp only [if_true, map_one, one_mul, sub_eq_zero] at hgate
  exact hgate

theorem lnPrev_eq (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz : R.κ 1 ≠ 0) (h5 : R.κ 5 = (R.κ 1)⁻¹) :
    ∀ (m : ℕ) (hm : m < R.n),
      lnPrevAt (R.env ⟨m, hm⟩) = R.ln0 * R.κ 0 ^ R.prefixExp m := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp only [prefixExp, Finset.range_zero, Finset.sum_empty, pow_zero, mul_one]
      rfl
  | succ m ih =>
      intro hm
      have hm' : m < R.n := by omega
      rw [← R.ln_chain ⟨m, hm'⟩ hm, R.ln_recurrence hchar hz h5 ⟨m, hm'⟩, ih hm',
        R.prefixExp_succ m hm', pow_add, mul_assoc]

def expOf (i : Fin R.n) (j : Fin 3) : ℕ := R.prefixExp i + (j : ℕ) + 1

theorem rowRecord_ts (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz : R.κ 1 ≠ 0) (h5 : R.κ 5 = (R.κ 1)⁻¹)
    (i : Fin R.n) (j : Fin 3) (hact : activeMask (R.env i) j = 1) :
    rowRecord (R.env i) j 7 = R.ln0 * R.κ 0 ^ R.expOf i j := by
  rw [rowRecord_ts_active _ j hact, R.alphaAt_eq, R.lnPrev_eq hchar hz h5 i i.isLt,
    expOf, mul_assoc, ← pow_add]
  rfl

def totalRequests : ℕ := R.prefixExp R.n

theorem expOf_pos (i : Fin R.n) (j : Fin 3) : 1 ≤ R.expOf i j := by
  unfold expOf; omega

theorem expOf_le_total (i : Fin R.n) (j : Fin 3) (hact : activeMask (R.env i) j = 1) :
    R.expOf i j ≤ R.totalRequests := by
  have h1 := active_lt_rowArity (R.env i) j hact
  have h2 : R.prefixExp ((i : ℕ) + 1) ≤ R.prefixExp R.n := R.prefixExp_mono i.isLt
  rw [R.prefixExp_succ i i.isLt, Fin.eta] at h2
  unfold expOf totalRequests
  omega

theorem expOf_lt_of_row_lt {i i' : Fin R.n} (hii : i < i') (j j' : Fin 3)
    (hact : activeMask (R.env i) j = 1) : R.expOf i j < R.expOf i' j' := by
  have h1 := active_lt_rowArity (R.env i) j hact
  have h2 : R.prefixExp ((i : ℕ) + 1) ≤ R.prefixExp i' := R.prefixExp_mono hii
  rw [R.prefixExp_succ i i.isLt, Fin.eta] at h2
  unfold expOf
  omega

theorem expOf_inj_row (i : Fin R.n) {j j' : Fin 3} (h : R.expOf i j = R.expOf i j') : j = j' := by
  unfold expOf at h
  exact Fin.ext (by omega)

theorem rowRequests_length (i : Fin R.n)
    (hbool : ∀ j : Fin 3, activeMask (R.env i) j = 0 ∨ activeMask (R.env i) j = 1)
    (h21 : activeMask (R.env i) 2 = 1 → activeMask (R.env i) 1 = 1) :
    (rowRequests (R.env i)).length = rowArity (R.env i) := by
  have h0 := activeMask_zero (R.env i)
  simp only [rowRequests, List.finRange, List.ofFn_succ, List.ofFn_zero, List.filterMap_cons,
    List.filterMap_nil, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, h0, if_true, rowArity]
  rcases hbool 2 with h2 | h2
  · rcases hbool 1 with h1 | h1
    · simp [h1, h2]
    · simp [h1, h2]
  · have h1 := h21 h2
    simp [h1, h2]

theorem active_two_imp_one (i : Fin R.n) (s : ComputeTable.State)
    (hsel : ∀ st, (R.env i).toSourceEnv.trace (opCol st) = ComputeTable.opSel s st) :
    activeMask (R.env i) 2 = 1 → activeMask (R.env i) 1 = 1 := by
  have h0 := hsel .s0; have h2 := hsel .s2; have h5 := hsel .s5; have h6 := hsel .s6
  have h7 := hsel .s7; have h8 := hsel .s8; have h9 := hsel .s9
  simp only [opCol] at h0 h2 h5 h6 h7 h8 h9
  simp only [activeMask, sampledActive, Expr.eval, Fin.isValue, Fin.val_one, Fin.val_two, h0, h2,
    h5, h6, h7, h8, h9]
  cases s <;> simp [ComputeTable.opSel]

theorem totalRequests_eq_length (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) :
    R.totalRequests = R.requests.length := by
  unfold totalRequests prefixExp requests
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn,
    ← Fin.sum_univ_eq_sum_range
      (fun k => if h : k < R.n then rowArity (R.env ⟨k, h⟩) else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨s, hsel⟩ := R.source_selector hchar i
  simp only [i.isLt, dite_true, Function.comp]
  rw [R.rowRequests_length i (fun j => R.activeMask_bool hchar i j)
    (R.active_two_imp_one i s hsel)]

theorem totalRequests_le : R.totalRequests ≤ 3 * R.n := by
  unfold totalRequests prefixExp
  calc (∑ k ∈ Finset.range R.n, if h : k < R.n then rowArity (R.env ⟨k, h⟩) else 0)
      ≤ ∑ _k ∈ Finset.range R.n, 3 := by
        refine Finset.sum_le_sum fun k _ => ?_
        split_ifs
        · exact rowArity_le _
        · omega
    _ = 3 * R.n := by simp [mul_comm]

section Nodup

variable [Fintype K] (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
  (hz : R.κ 1 ≠ 0) (h5 : R.κ 5 = (R.κ 1)⁻¹)
  (hα : R.κ 0 ∉ TimestampCollisionEvent R.totalRequests)
include hchar hz h5 hα

theorem expOf_eq_of_ts_eq {i i' : Fin R.n} {j j' : Fin 3}
    (hact : activeMask (R.env i) j = 1) (hact' : activeMask (R.env i') j' = 1)
    (h : rowRecord (R.env i) j 7 = rowRecord (R.env i') j' 7) :
    R.expOf i j = R.expOf i' j' := by
  rw [R.rowRecord_ts hchar hz h5 i j hact, R.rowRecord_ts hchar hz h5 i' j' hact'] at h
  have hpow := mul_left_cancel₀ (by rw [R.ln0_eq_one]; exact one_ne_zero) h
  exact pow_inj_of_not_collision hα (R.expOf_pos i j) (R.expOf_le_total i j hact)
    (R.expOf_pos i' j') (R.expOf_le_total i' j' hact') hpow

theorem rowRequests_nodup (i : Fin R.n) : (rowRequests (R.env i)).Nodup := by
  unfold rowRequests
  refine List.Nodup.filterMap ?_ (List.nodup_finRange 3)
  intro j j' r hj hj'
  by_cases ha : activeMask (R.env i) j = 1
  · rw [if_pos ha] at hj
    by_cases ha' : activeMask (R.env i) j' = 1
    · rw [if_pos ha'] at hj'
      have hr : rowRecord (R.env i) j = rowRecord (R.env i) j' :=
        (Option.some_inj.mp hj).trans (Option.some_inj.mp hj').symm
      exact R.expOf_inj_row i (R.expOf_eq_of_ts_eq hchar hz h5 hα ha ha' (congrFun hr 7))
    · rw [if_neg ha'] at hj'; cases hj'
  · rw [if_neg ha] at hj; cases hj

theorem rowRequests_disjoint {i i' : Fin R.n} (hii : i < i') :
    List.Disjoint (rowRequests (R.env i)) (rowRequests (R.env i')) := by
  intro r hr hr'
  simp only [rowRequests, List.mem_filterMap, List.mem_finRange, true_and] at hr hr'
  obtain ⟨j, hj⟩ := hr
  obtain ⟨j', hj'⟩ := hr'
  by_cases ha : activeMask (R.env i) j = 1
  · by_cases ha' : activeMask (R.env i') j' = 1
    · rw [if_pos ha] at hj
      rw [if_pos ha'] at hj'
      have hr : rowRecord (R.env i) j = rowRecord (R.env i') j' :=
        (Option.some_inj.mp hj).trans (Option.some_inj.mp hj').symm
      have heq := R.expOf_eq_of_ts_eq hchar hz h5 hα ha ha' (congrFun hr 7)
      have hlt := R.expOf_lt_of_row_lt hii j j' ha
      omega
    · rw [if_neg ha'] at hj'; cases hj'
  · rw [if_neg ha] at hj; cases hj

theorem requests_nodup_of_total : R.requests.Nodup := by
  unfold requests
  rw [List.nodup_flatten]
  constructor
  · intro l hl
    rw [List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    exact R.rowRequests_nodup hchar hz h5 hα i
  · rw [List.pairwise_ofFn]
    intro i i' hii
    exact R.rowRequests_disjoint hchar hz h5 hα hii

end Nodup

/-- **Unique requests, package-free**: outside
`TimestampCollisionEvent |requests|` at the timestamp coin `κ 0`, the committed request list
is duplicate-free. -/
theorem requests_nodup [Fintype K] (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz : R.κ 1 ≠ 0) (h5 : R.κ 5 = (R.κ 1)⁻¹)
    (hα : R.κ 0 ∉ TimestampCollisionEvent R.requests.length) :
    R.requests.Nodup := by
  rw [← R.totalRequests_eq_length hchar] at hα
  exact R.requests_nodup_of_total hchar hz h5 hα

end IORows

/-! ## 4. The instance at the un-hosted compute chip, at any public map -/

section At309

variable [Fintype K] [Fintype F] [DecidableEq K]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (hinj : Function.Injective nodes)
  (b : Basis (Fin 3) F K) (pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
  (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
  (c : OptimizedProductionChallengeTuple K F)

theorem computeChipAt309_w : (computeChipAt309 hn nodes b pubVal orbit c).rap.w = 309 := rfl

/-- The gathered row environment of a 309 trace at row `i`. -/
abbrev env309 (Qc : Fin (computeChipAt309 hn nodes b pubVal orbit c).rap.w → F[X]) (i : Fin n) :
    CorrectedFinalTypedEnv F K :=
  gatherCorrectedFinalTypedEnv b
    (envOfTrace Qc orbit.ω (nodes i) (computeChalValOfTuple b c) pubVal)

theorem env309_chal (Qc : Fin (computeChipAt309 hn nodes b pubVal orbit c).rap.w → F[X])
    (i : Fin n) (q : ℕ) (hq : q < 12) :
    (env309 hn nodes b pubVal orbit c Qc i).toSourceEnv.chal q = computeKOfTuple c q := by
  simp only [CorrectedFinalTypedEnv.toSourceEnv, gatherCorrectedFinalTypedEnv,
    envOfTrace, hq, ↓reduceDIte]
  change (∑ k : Fin 3, computeChalValOfTuple b c (3 * q + (k : ℕ)) • b k) = computeKOfTuple c q
  have hslot : ∀ k : Fin 3, 3 * q + (k : ℕ) < 36 := by intro k; omega
  have hcoord : ∀ k : Fin 3,
      computeChalValOfTuple b c (3 * q + (k : ℕ)) = coord b (computeKOfTuple c q) k := by
    intro k
    simp only [computeChalValOfTuple, hslot k, ↓reduceIte]
    have hdiv : (3 * q + (k : ℕ)) / 3 = q := by omega
    have hmod : (3 * q + (k : ℕ)) % 3 = (k : ℕ) := by omega
    rw [hdiv]
    apply congrArg
    exact Fin.ext hmod
  simp_rw [hcoord]
  exact reconstruct_coord b (computeKOfTuple c q)

/-- The terminal public gathered at any row is the public map's block `6..8`. -/
theorem env309_requests (Qc : Fin (computeChipAt309 hn nodes b pubVal orbit c).rap.w → F[X])
    (i : Fin n) :
    (env309 hn nodes b pubVal orbit c Qc i).extensionPublic 2 =
      ∑ k : Fin 3, pubVal (6 + (k : ℕ)) • b k := by
  simp only [gatherCorrectedFinalTypedEnv, envOfTrace]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2

include hinj hadj in
/-- **The row family of an accepted 309 compute trace**, at any nodes / basis / orbit / public
map and any tuple `c`.  `κ = computeKOfTuple c`. -/
def rows309 (Qc : Fin (computeChipAt309 hn nodes b pubVal orbit c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipAt309 hn nodes b pubVal orbit c) Qc) :
    IORows F K where
  n := n
  hn := hn
  env := env309 hn nodes b pubVal orbit c Qc
  envF := fun i => envOfTrace Qc orbit.ω (nodes i) (computeChalValOfTuple b c) pubVal
  obl := fun i => by
    have hl := (satisfies309_iff_sourceLanguage hn nodes b (computeChalValOfTuple b c) pubVal
      orbit Qc).1 hsat
    exact IORowObligations.of309 (hl.2 _ (by simp [rowNodeSet]))
  first := fun i => by
    have hl := (satisfies309_iff_sourceLanguage hn nodes b (computeChalValOfTuple b c) pubVal
      orbit Qc).1 hsat
    have h0 := hl.1 ⟨0, by change 0 < 2; norm_num⟩
    have h11 : 11 < (computeChipAt309 hn nodes b pubVal orbit c).rap.w := by
      rw [computeChipAt309_w]; norm_num
    have hc0 : (ProductionNamedComputeRAP309 hn nodes b (computeChalValOfTuple b c) pubVal
        orbit).preprocessingColumn ⟨0, by change 0 < 2; norm_num⟩ = ⟨11, h11⟩ := rfl
    rw [hc0] at h0
    show (envOfTrace Qc orbit.ω (nodes i) (computeChalValOfTuple b c) pubVal).trace 11 = _
    simp only [envOfTrace, dif_pos h11]
    rw [show (Qc ⟨11, h11⟩) = Nock.Framework.firstRowMask nodes from h0,
      Nock.Framework.firstRowMask_eval _ hinj]
  last := fun i => by
    have hl := (satisfies309_iff_sourceLanguage hn nodes b (computeChalValOfTuple b c) pubVal
      orbit Qc).1 hsat
    have h1 := hl.1 ⟨1, by change 1 < 2; norm_num⟩
    have h12 : 12 < (computeChipAt309 hn nodes b pubVal orbit c).rap.w := by
      rw [computeChipAt309_w]; norm_num
    have hc1 : (ProductionNamedComputeRAP309 hn nodes b (computeChalValOfTuple b c) pubVal
        orbit).preprocessingColumn ⟨1, by change 1 < 2; norm_num⟩ = ⟨12, h12⟩ := rfl
    rw [hc1] at h1
    show (envOfTrace Qc orbit.ω (nodes i) (computeChalValOfTuple b c) pubVal).trace 12 = _
    simp only [envOfTrace, dif_pos h12]
    rw [show (Qc ⟨12, h12⟩) = Nock.Framework.lastRowMask hn nodes from h1,
      Nock.Framework.lastRowMask_eval _ _ hinj]
    by_cases hi : (i : ℕ) + 1 = n
    · rw [if_pos hi, if_pos (Fin.ext (by simp; omega))]
    · rw [if_neg hi, if_neg (fun heq => hi (by have := congrArg Fin.val heq; simp at this; omega))]
  next := fun i hi r => by
    simp only [env309, gatherCorrectedFinalTypedEnv]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hlt : correctedFinalExtCoordIndex (e := 3) r k <
        (computeChipAt309 hn nodes b pubVal orbit c).rap.w := by
      rw [computeChipAt309_w]; simp [correctedFinalExtCoordIndex]; omega
    simp only [envOfTrace, dif_pos hlt]
    rw [hadj i hi]
  κ := computeKOfTuple c
  chal := fun i q hq => env309_chal hn nodes b pubVal orbit c Qc i q hq

end At309

end

end Nock.NockVMROM.Thm54.SVIO
