import Nock.NockVMROM.Thm54.Unhosted309Semantics
import Nock.NockVMROM.Thm54.Unhosted309Codec
import Nock.NockVMROM.Thm54.Unhosted309Insensitive
import Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction

/-!
# The honest fill at width 309 and its canonical satisfaction

Downstream of `TraceGen/Gen.lean` (zero edits there); parallel definitions;
nothing existing is edited.**

`correctedCanonicalFinalTrace309` is the deployed canonical trace (`correctedCanonicalFinalTrace`)
with three changes, and nothing else:

* the 24 physical columns of the eight former walk-host `𝕂`-roles carry the **309 encoding**
  (`sampledEncode309`): on a row of state `s` the two host roles of `s` hold the genuine
  fingerprint coordinates instead of `count`/`acc`; on the other rows the cell is unchanged;
* the walk `count`/`acc` (`A.exact.computeWalk`, the same assignment) are interpolated into the
  new columns `W0 = 303..305`, `W1 = 306..308`;
* the residual roles `58`/`59` interpolate the **retargeted** walk recurrences.

`canonical_satisfies309` is proved by *transfer* from the deployed canonical satisfaction
(`OptimizedComputeCanonicalSatisfaction.canonical_corrected_source_obligations`, same
hypotheses): every untouched source is host-insensitive (`Unhosted309Insensitive`), so it
evaluates identically on the two traces; the seven retargeted sources read `W0`/`W1` where the
deployed sources read the hosted overlay, and those agree value-for-value.
`SampledIOSameExecutionAssignment.witness10` / `witness10_accepts` are used through the deployed
theorem unchanged (they read no walk host).

Paper: the paper.
-/

namespace Nock.NockVMROM.Thm54
namespace Unhosted309

open Nock
open Nock.Reified
open Nock.Framework Reify
open Module
open OptimizedComputeGateBasis
open OptimizedComputeCorrectedFinal
open OptimizedComputeFinal hiding residualWitnessRole ResidualWitnessId FinalExtensionColumn
open OptimizedComputeFinalTypedLowering
open OptimizedComputeFinalTrace
open OptimizedComputeSemanticRealization
open OptimizedComputeSameExecution
open OptimizedComputeSubstitution
open OptimizedComputeSampledTrace
open OptimizedComputeOverlay
open OptimizedComputeTemplate
open OptimizedComputeCanonicalSatisfaction
open OptimizedComputeCodec (decodeState)
open StrictExtension
open CoordinateBasis
open CoordinateCompiler
open OptimizedComputeBaseGates
open MonolithicRAP
open ComputePaperPacking
open scoped Polynomial

set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K] [DecidableEq F]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-! ## 1. The 309 honest row and the column classes -/

/-- The walk values of row `i`: `count(i+1)`, `acc(i+1)`. -/
def walkVal309 (A : SampledIOSameExecutionAssignment R p) (i : Fin R.problem.cfg.compRows) :
    Fin 2 → K :=
  ![A.exact.computeWalk.count ((i : ℕ) + 1), A.exact.computeWalk.acc ((i : ℕ) + 1)]

/-- **The honest 309 row**: the same execution, table auxiliary and overlay as the deployed
`encodedRowAt`, encoded by `sampledEncode309`. -/
def encodedRowAt309 (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) : Row309 F K :=
  sampledEncode309 (R.problem.exec.computePubAt i) (R.problem.exec.computeDecAt i)
    (A.exact.computeTableAux i) (overlayAt A i)

theorem encodedRowAt309_walk (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) :
    (encodedRowAt309 (F := F) A i).walk = walkVal309 A i := by
  funext j; fin_cases j <;> rfl

/-- A physical column of a former walk-host `𝕂`-role. -/
def isHostCol (j : ℕ) : Bool := decide (13 ≤ j ∧ j < 202 ∧ (j - 13) / 3 ∈ hostKRoles)

/-- A physical column of the residual roles `58`/`59`. -/
def isResCol (j : ℕ) : Bool := decide (13 ≤ j ∧ j < 202 ∧ ((j - 13) / 3 = 58 ∨ (j - 13) / 3 = 59))

theorem isHostCol_role {j : ℕ} (h : isHostCol j = true) : (j - 13) / 3 < 58 := by
  simp only [isHostCol, hostKRoles, decide_eq_true_eq, List.mem_cons, List.not_mem_nil,
    or_false] at h
  omega

/-- The 309 cell of a host column: coordinate `k` of the 309-encoded `𝕂` role. -/
def hostCell309 (A : SampledIOSameExecutionAssignment R p) (b : Basis (Fin 3) F K)
    (i : Fin R.problem.cfg.compRows) (j : ℕ) : F :=
  if h : (j - 13) / 3 < 58 then
    coord b (coreExtensionValue (encodedRowAt309 (F := F) A i).row ⟨(j - 13) / 3, h⟩)
      ⟨(j - 13) % 3, Nat.mod_lt _ (by omega)⟩
  else 0

/-- Interpolation of node values. -/
def interp {n : ℕ} (nodes : Fin n → F) (f : Fin n → F) : F[X] :=
  Lagrange.interpolate Finset.univ nodes f

theorem interp_eval {n : ℕ} (nodes : Fin n → F) (hnodes : Function.Injective nodes)
    (f : Fin n → F) (i : Fin n) : (interp nodes f).eval (nodes i) = f i :=
  Lagrange.eval_interpolate_at_node _ hnodes.injOn (Finset.mem_univ i)

/-- The walk-column polynomial of physical column `303 + 3·jj + k`. -/
def walkPoly (A : SampledIOSameExecutionAssignment R p) (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (j : ℕ) : F[X] :=
  interp nodes fun i =>
    if h : (j - 303) / 3 < 2 then
      coord b (walkVal309 A i ⟨(j - 303) / 3, h⟩) ⟨(j - 303) % 3, Nat.mod_lt _ (by omega)⟩
    else 0

/-! ## 2. The preliminary and canonical 309 traces -/

/-- **Stage one at 309**: the deployed preliminary trace, with the host columns re-encoded and
the walk columns appended. -/
def preliminaryTrace309 (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) : Fin 309 → F[X] := fun j =>
  if 303 ≤ (j : ℕ) then walkPoly A nodes b j
  else if isHostCol j then interp nodes fun i => hostCell309 A b i j
  else if h : (j : ℕ) < 302 then preliminaryTrace A hn nodes b ⟨j, h⟩
  else 0

/-- The retargeted residual polynomial (roles `58`/`59`). -/
def residualPoly309 (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h) (r : Fin 2) (k : Fin 3) : F[X] :=
  interp nodes fun i => (compile309 b (residualSource309 r) k).eval
    (envOfTrace (preliminaryTrace309 A hn nodes b) orbit.ω (nodes i) chalVal pubVal)

/-- **`correctedCanonicalFinalTrace309`** — the honest 309 trace. -/
def correctedCanonicalFinalTrace309 (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h) : Fin 309 → F[X] := fun j =>
  if 303 ≤ (j : ℕ) then walkPoly A nodes b j
  else if isHostCol j then interp nodes fun i => hostCell309 A b i j
  else if hR : isResCol j then
    residualPoly309 A hn nodes b chalVal pubVal orbit
      ⟨(j - 13) / 3 - 58, by simp [isResCol] at hR; omega⟩
      ⟨(j - 13) % 3, Nat.mod_lt _ (by omega)⟩
  else if h : (j : ℕ) < 303 then
    correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit ⟨j, h⟩
  else 0

/-! ## 3. Cell-level relations to the deployed canonical trace -/

section Cells
variable [FiniteDimensional F K]
variable (A : SampledIOSameExecutionAssignment R p)
  (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
  (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
  {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)

/-- The state of row `i`. -/
abbrev stAt (i : Fin R.problem.cfg.compRows) : ComputeTable.State :=
  (R.problem.exec.computePubAt i).state

theorem overlayRoleA_val (st : ComputeTable.State) :
    ((overlayRoleA st : Fin 12) : ℕ) = overlayANat st := by
  cases st <;> rfl

theorem stOfIdx_stateIndex (st : ComputeTable.State) :
    stOfIdx (OptimizedComputeCodec.stateIndex st) = st := by
  cases st <;> rfl

/-- **The codec relation**: off the two host roles of the row's state, the 309-encoded core
value is the deployed one. -/
theorem coreExt309_eq (i : Fin R.problem.cfg.compRows) (r : Fin 58)
    (hr : (r : ℕ) ∉ hostRolesOf (stAt i)) :
    coreExtensionValue (encodedRowAt309 (F := F) A i).row r =
      coreExtensionValue (encodedRowAt (F := F) A i) r := by
  unfold coreExtensionValue
  split_ifs with h36
  · simp only [encodedRowAt309, sampledEncode309, encodedRowAt, sampledEncode]
    apply sampledEncodeExtension309_eq_of_not_host
    intro r' c heq ⟨hrA, hc⟩
    simp only [Sum.inl.injEq, Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    apply hr
    have hv1 : (r' : ℕ) = (r : ℕ) / 3 := by rw [← h1]
    have hv2 : (c : ℕ) = (r : ℕ) % 3 := by rw [← h2]
    have hA : (r' : ℕ) = overlayANat (stAt i) := by rw [hrA, overlayRoleA_val]
    have hc2 : (c : ℕ) ≠ 2 := fun h => hc (Fin.ext h)
    have hclt : (c : ℕ) < 3 := c.isLt
    simp only [hostRolesOf, List.mem_cons, List.not_mem_nil, or_false]
    omega
  · rfl
  · rfl

/-- At the host roles of the row's state the 309 core value is the genuine fingerprint. -/
theorem hostCell309_eq_old (i : Fin R.problem.cfg.compRows) (j : ℕ)
    (hr : (j - 13) / 3 ∉ hostRolesOf (stAt i)) (hlt : (j - 13) / 3 < 58) :
    hostCell309 A b i j = coord b (coreExtensionValue (encodedRowAt (F := F) A i)
      ⟨(j - 13) / 3, hlt⟩) ⟨(j - 13) % 3, Nat.mod_lt _ (by omega)⟩ := by
  simp only [hostCell309, dif_pos hlt]
  rw [coreExt309_eq A i _ hr]

/-- The deployed canonical cell of a pre-Form-R non-residual core column. -/
theorem old_core_cell (hnodes : Function.Injective nodes) (i : Fin R.problem.cfg.compRows) (j : ℕ) (h13 : 13 ≤ j) (h202 : j < 202)
    (hR : isResCol j = false) (hlt : (j - 13) / 3 < 58) :
    (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit ⟨j, by omega⟩).eval
        (nodes i) =
      coord b (coreExtensionValue (encodedRowAt (F := F) A i) ⟨(j - 13) / 3, hlt⟩)
        ⟨(j - 13) % 3, Nat.mod_lt _ (by omega)⟩ := by
  rw [correctedCanonicalFinalTrace_eval_preFormR A hn nodes hnodes b chalVal pubVal orbit i _
    (by simpa using h202)]
  have hnr : ¬ (13 ≤ j ∧ (j - 13) / 3 < 60 ∧ 58 ≤ (j - 13) / 3) := by
    simp [isResCol] at hR; omega
  simp only [hnr, dif_neg, not_false_eq_true]
  have h13' : ¬ j < 13 := by omega
  simp only [preliminaryCell, h13', dif_neg, not_false_eq_true, hlt, dif_pos]

theorem old_pre_core_cell (hnodes : Function.Injective nodes) (i : Fin R.problem.cfg.compRows) (j : ℕ) (h13 : 13 ≤ j)
    (h202 : j < 202) (hlt : (j - 13) / 3 < 58) :
    (preliminaryTrace A hn nodes b ⟨j, by omega⟩).eval (nodes i) =
      coord b (coreExtensionValue (encodedRowAt (F := F) A i) ⟨(j - 13) / 3, hlt⟩)
        ⟨(j - 13) % 3, Nat.mod_lt _ (by omega)⟩ := by
  rw [preliminaryTrace_eval A hn nodes hnodes b i]
  have h13' : ¬ j < 13 := by omega
  simp only [preliminaryCell, h13', dif_neg, not_false_eq_true, hlt, dif_pos]

/-- Polynomial equality off the host, residual and walk columns. -/
theorem trace309_eq_old (j : Fin 309) (h303 : (j : ℕ) < 303) (hH : isHostCol j = false)
    (hR : isResCol j = false) :
    correctedCanonicalFinalTrace309 A hn nodes b chalVal pubVal orbit j =
      correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit ⟨j, h303⟩ := by
  have h1 : ¬ 303 ≤ (j : ℕ) := by omega
  simp [correctedCanonicalFinalTrace309, h1, hH, hR, h303]

theorem pre309_eq_old (j : Fin 309) (h302 : (j : ℕ) < 302) (hH : isHostCol j = false) :
    preliminaryTrace309 A hn nodes b j = preliminaryTrace A hn nodes b ⟨j, h302⟩ := by
  have h1 : ¬ 303 ≤ (j : ℕ) := by omega
  simp [preliminaryTrace309, h1, hH, h302]

theorem pre309_302 : preliminaryTrace309 A hn nodes b ⟨302, by omega⟩ = 0 := by
  simp [preliminaryTrace309, isHostCol]

/-- The final and preliminary 309 traces agree off the residual and Form R/`S` columns. -/
theorem trace309_eq_pre309 (j : Fin 309) (hj : (j : ℕ) < 202 ∨ 303 ≤ (j : ℕ))
    (hR : isResCol j = false) :
    correctedCanonicalFinalTrace309 A hn nodes b chalVal pubVal orbit j =
      preliminaryTrace309 A hn nodes b j := by
  by_cases hW : 303 ≤ (j : ℕ)
  · simp [correctedCanonicalFinalTrace309, preliminaryTrace309, hW]
  have h202 : (j : ℕ) < 202 := by omega
  by_cases hH : isHostCol j = true
  · simp [correctedCanonicalFinalTrace309, preliminaryTrace309, hW, hH]
  · have hH' : isHostCol j = false := by simpa using hH
    simp only [correctedCanonicalFinalTrace309, preliminaryTrace309, hW, if_false, hH',
      Bool.false_eq_true, hR, dif_neg, not_false_eq_true,
      show (j : ℕ) < 303 by omega, show (j : ℕ) < 302 by omega, dif_pos]
    simp only [correctedCanonicalFinalTrace]
    have h296 : ¬ (296 ≤ (j : ℕ) ∧ (j : ℕ) < 299) := by omega
    have h299 : ¬ 299 ≤ (j : ℕ) := by omega
    have hnr : ¬ (13 ≤ (j : ℕ) ∧ ((j : ℕ) - 13) / 3 < 60 ∧ 58 ≤ ((j : ℕ) - 13) / 3) := by
      simp [isResCol] at hR; omega
    simp only [h296, h299, hnr, dif_neg, not_false_eq_true]

end Cells

/-! ## 4. Physical-environment relations -/

section Envs
variable [FiniteDimensional F K]
variable (A : SampledIOSameExecutionAssignment R p)
  (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
  (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
  {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)

/-- The new and the deployed canonical row environments. -/
abbrev envNew (x : F) : Env F :=
  envOfTrace (correctedCanonicalFinalTrace309 A hn nodes b chalVal pubVal orbit) orbit.ω x
    chalVal pubVal
abbrev envOld (x : F) : Env F :=
  envOfTrace (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit) orbit.ω x
    chalVal pubVal
abbrev envNewPre (x : F) : Env F :=
  envOfTrace (preliminaryTrace309 A hn nodes b) orbit.ω x chalVal pubVal
abbrev envOldPre (x : F) : Env F :=
  envOfTrace (preliminaryTrace A hn nodes b) orbit.ω x chalVal pubVal

/-- **Current row**: the two canonical rows agree off the residual columns and the host roles of
the row's state (and the walk columns). -/
theorem envNew_trace_eq (hnodes : Function.Injective nodes) (i : Fin R.problem.cfg.compRows)
    (c : ℕ) (h303 : c < 303) (hR : isResCol c = false)
    (hH : isHostCol c = true → (c - 13) / 3 ∉ hostRolesOf (stAt i)) :
    (envNew A hn nodes b chalVal pubVal orbit (nodes i)).trace c =
      (envOld A hn nodes b chalVal pubVal orbit (nodes i)).trace c := by
  simp only [envNew, envOld, envOfTrace, dif_pos (show c < 309 by omega), dif_pos h303]
  by_cases hh : isHostCol c = true
  · have hlt := isHostCol_role hh
    have h13 : 13 ≤ c ∧ c < 202 := by simp [isHostCol] at hh; omega
    have hns : ¬ 303 ≤ c := by omega
    simp only [correctedCanonicalFinalTrace309, hns, if_false, hh, if_true]
    rw [interp_eval nodes hnodes, hostCell309_eq_old A b i c (hH hh) hlt,
      old_core_cell A hn nodes b chalVal pubVal orbit hnodes i c h13.1 h13.2 hR hlt]
  · have hh' : isHostCol c = false := by simpa using hh
    rw [trace309_eq_old A hn nodes b chalVal pubVal orbit ⟨c, by omega⟩ h303 hh' hR]

/-- **Successor row**: the canonical rows agree off the residual and all host columns. -/
theorem envNew_traceNext_eq (c : ℕ) (h303 : c < 303) (hR : isResCol c = false)
    (hH : isHostCol c = false) (x : F) :
    (envNew A hn nodes b chalVal pubVal orbit x).traceNext c =
      (envOld A hn nodes b chalVal pubVal orbit x).traceNext c := by
  simp only [envNew, envOld, envOfTrace, dif_pos (show c < 309 by omega), dif_pos h303]
  rw [trace309_eq_old A hn nodes b chalVal pubVal orbit ⟨c, by omega⟩ h303 hH hR]

theorem envNew_trace_eq_of_not_host (c : ℕ) (h303 : c < 303) (hR : isResCol c = false)
    (hH : isHostCol c = false) (x : F) :
    (envNew A hn nodes b chalVal pubVal orbit x).trace c =
      (envOld A hn nodes b chalVal pubVal orbit x).trace c := by
  simp only [envNew, envOld, envOfTrace, dif_pos (show c < 309 by omega), dif_pos h303]
  rw [trace309_eq_old A hn nodes b chalVal pubVal orbit ⟨c, by omega⟩ h303 hH hR]

/-- The two preliminary traces, current row. -/
theorem envNewPre_trace_eq (hnodes : Function.Injective nodes) (i : Fin R.problem.cfg.compRows)
    (c : ℕ) (h303 : c < 303)
    (hH : isHostCol c = true → (c - 13) / 3 ∉ hostRolesOf (stAt i)) :
    (envNewPre A hn nodes b chalVal pubVal orbit (nodes i)).trace c =
      (envOldPre A hn nodes b chalVal pubVal orbit (nodes i)).trace c := by
  simp only [envNewPre, envOldPre, envOfTrace, dif_pos (show c < 309 by omega)]
  by_cases hh : isHostCol c = true
  · have hlt := isHostCol_role hh
    have h13 : 13 ≤ c ∧ c < 202 := by simp [isHostCol] at hh; omega
    have hns : ¬ 303 ≤ c := by omega
    simp only [preliminaryTrace309, hns, if_false, hh, if_true, dif_pos (show c < 302 by omega)]
    rw [interp_eval nodes hnodes, hostCell309_eq_old A b i c (hH hh) hlt,
      old_pre_core_cell A hn nodes b hnodes i c h13.1 h13.2 hlt]
  · have hh' : isHostCol c = false := by simpa using hh
    by_cases h302 : c < 302
    · rw [dif_pos h302, pre309_eq_old A hn nodes b ⟨c, by omega⟩ h302 hh']
    · have hc : c = 302 := by omega
      subst hc
      rw [dif_neg h302]
      show Polynomial.eval _ (preliminaryTrace309 A hn nodes b ⟨302, by omega⟩) = _
      rw [pre309_302]; simp

/-- The two preliminary traces, successor row, at a nonterminal row. -/
theorem envNewPre_traceNext_eq (hnodes : Function.Injective nodes)
    (i : Fin R.problem.cfg.compRows) (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (c : ℕ) (h303 : c < 303)
    (hH : isHostCol c = true → (c - 13) / 3 ∉ hostRolesOf (stAt ⟨(i : ℕ) + 1, hi⟩)) :
    (envNewPre A hn nodes b chalVal pubVal orbit (nodes i)).traceNext c =
      (envOldPre A hn nodes b chalVal pubVal orbit (nodes i)).traceNext c := by
  have h := envNewPre_trace_eq A hn nodes b chalVal pubVal orbit hnodes ⟨(i : ℕ) + 1, hi⟩ c h303 hH
  simp only [envNewPre, envOldPre, envOfTrace] at h ⊢
  rw [← hsucc]
  exact h

/-- The final and preliminary 309 rows agree off the residual and Form R / `S` columns. -/
theorem envNew_eq_pre (c : ℕ) (hc : c < 202 ∨ 303 ≤ c) (hR : isResCol c = false) (x : F) :
    (envNew A hn nodes b chalVal pubVal orbit x).trace c =
        (envNewPre A hn nodes b chalVal pubVal orbit x).trace c ∧
      (envNew A hn nodes b chalVal pubVal orbit x).traceNext c =
        (envNewPre A hn nodes b chalVal pubVal orbit x).traceNext c := by
  simp only [envNew, envNewPre, envOfTrace]
  by_cases h309 : c < 309
  · have he := trace309_eq_pre309 A hn nodes b chalVal pubVal orbit ⟨c, h309⟩ hc hR
    simp only [dif_pos h309, he]
    exact ⟨trivial, trivial⟩
  · simp only [dif_neg h309]
    exact ⟨trivial, trivial⟩

end Envs

/-! ## 5. From physical columns to the decoded source environment -/

/-- The physical columns a source index `j` of the 309 decode reads. -/
def physOf (j c : ℕ) : Prop :=
  (j < 13 ∧ c = j) ∨ (13 ≤ j ∧ j < 76 ∧ 13 + 3 * (j - 13) ≤ c ∧ c < 16 + 3 * (j - 13)) ∨
    (202 ≤ j ∧ j < 296 ∧ c = j) ∨ (j = 296 ∧ 296 ≤ c ∧ c < 299) ∨
    (j = 299 ∧ 299 ≤ c ∧ c < 302) ∨ (j = 302 ∧ c = 302) ∨
    (j = 303 ∧ 303 ≤ c ∧ c < 306) ∨ (j = 306 ∧ 306 ≤ c ∧ c < 309)

theorem src_trace_congr [FiniteDimensional F K] (b : Basis (Fin 3) F K) {E₁ E₂ : Env F} (j : ℕ)
    (h : ∀ c, physOf j c → E₁.trace c = E₂.trace c) :
    (gather309 b E₁).toSourceEnv.trace j = (gather309 b E₂).toSourceEnv.trace j := by
  simp only [Env309.toSourceEnv, gather309, CorrectedFinalTypedEnv.toSourceEnv,
    gatherCorrectedFinalTypedEnv, correctedFinalExtCoordIndex, walkLimb]
  split_ifs <;>
    first
    | rfl
    | (rw [h j (by unfold physOf; omega)])
    | (apply Finset.sum_congr rfl; intro k _; rw [h _ (by unfold physOf; have := k.isLt; omega)])
    | (rw [h _ (by unfold physOf; omega)])

theorem src_traceNext_congr [FiniteDimensional F K] (b : Basis (Fin 3) F K) {E₁ E₂ : Env F}
    (j : ℕ) (h : ∀ c, physOf j c → E₁.traceNext c = E₂.traceNext c) :
    (gather309 b E₁).toSourceEnv.traceNext j = (gather309 b E₂).toSourceEnv.traceNext j := by
  simp only [Env309.toSourceEnv, gather309, CorrectedFinalTypedEnv.toSourceEnv,
    gatherCorrectedFinalTypedEnv, correctedFinalExtCoordIndex, walkLimb]
  split_ifs <;>
    first
    | rfl
    | (rw [h j (by unfold physOf; omega)])
    | (apply Finset.sum_congr rfl; intro k _; rw [h _ (by unfold physOf; have := k.isLt; omega)])
    | (rw [h _ (by unfold physOf; omega)])

theorem src_chal_eq (b : Basis (Fin 3) F K) {E₁ E₂ : Env F} (h : E₁.chal = E₂.chal) (j : ℕ) :
    (gather309 b E₁).toSourceEnv.chal j = (gather309 b E₂).toSourceEnv.chal j := by
  simp [Env309.toSourceEnv, gather309, CorrectedFinalTypedEnv.toSourceEnv,
    gatherCorrectedFinalTypedEnv, h]

theorem src_pub_eq (b : Basis (Fin 3) F K) {E₁ E₂ : Env F} (h : E₁.pub = E₂.pub) (j : ℕ) :
    (gather309 b E₁).toSourceEnv.pub j = (gather309 b E₂).toSourceEnv.pub j := by
  simp [Env309.toSourceEnv, gather309, CorrectedFinalTypedEnv.toSourceEnv,
    gatherCorrectedFinalTypedEnv, h]

/-! ## 6. Source-level agreement and the untouched-gate transfer -/

section Transfer
variable [FiniteDimensional F K]
variable (A : SampledIOSameExecutionAssignment R p)
  (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
  (hnodes : Function.Injective nodes)
  (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
  {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)

/-- The decoded new and deployed canonical rows. -/
abbrev srcNew (i : Fin R.problem.cfg.compRows) : Env K :=
  (gather309 b (envNew A hn nodes b chalVal pubVal orbit (nodes i))).toSourceEnv
abbrev srcOld (i : Fin R.problem.cfg.compRows) : Env K :=
  (gather309 b (envOld A hn nodes b chalVal pubVal orbit (nodes i))).toSourceEnv

/-- The state index of row `i`. -/
abbrev sIdx (i : Fin R.problem.cfg.compRows) : Fin 11 :=
  OptimizedComputeCodec.stateIndex (stAt i)

include hnodes in
theorem envOld_selector (i : Fin R.problem.cfg.compRows) (j : ℕ) (hj : j < 11) :
    (envOld A hn nodes b chalVal pubVal orbit (nodes i)).trace j =
      if j = (sIdx i : ℕ) then 1 else 0 := by
  have h1 := correctedCanonicalFinalTrace_base_eval A hn nodes hnodes b chalVal pubVal orbit i
    ⟨j, by omega⟩
  have h2 := finalBaseCell_selector A hn i ⟨j, hj⟩
  simp only [envOld] at h1 ⊢
  rw [show (⟨j, by omega⟩ : Fin 13) = ⟨((⟨j, hj⟩ : Fin 11) : ℕ),
    Nat.lt_trans (⟨j, hj⟩ : Fin 11).isLt eleven_lt_thirteen⟩ from rfl] at h1
  rw [h1, h2]
  simp [Fin.ext_iff]

include hnodes in
theorem envNew_selector (i : Fin R.problem.cfg.compRows) (j : ℕ) (hj : j < 11) :
    (envNew A hn nodes b chalVal pubVal orbit (nodes i)).trace j =
      if j = (sIdx i : ℕ) then 1 else 0 := by
  rw [envNew_trace_eq A hn nodes b chalVal pubVal orbit hnodes i j (by omega)
    (by simp [isResCol]; omega) (by simp [isHostCol]; omega)]
  exact envOld_selector A hn nodes hnodes b chalVal pubVal orbit i j hj

theorem matches_curSel_of {E : Env F} {s : Fin 11}
    (hsel : ∀ j, j < 11 → E.trace j = if j = (s : ℕ) then 1 else 0) :
    Matches (curSel s) (gather309 b E).toSourceEnv := by
  intro k j v hσ
  cases k <;> simp only [curSel, reduceCtorEq] at hσ
  by_cases hj : j < 11
  · simp only [hj, if_true, Option.some.injEq] at hσ
    subst hσ
    have h13 : j < 13 := by omega
    simp only [varVal, Env309.toSourceEnv, gather309, CorrectedFinalTypedEnv.toSourceEnv,
      gatherCorrectedFinalTypedEnv, show j ≠ 303 by omega, show j ≠ 306 by omega, if_false,
      dif_pos h13, hsel j hj]
    split_ifs <;> simp
  · simp [hj] at hσ

include hnodes in
theorem matches_new (i : Fin R.problem.cfg.compRows) :
    Matches (curSel (sIdx i)) (srcNew A hn nodes b chalVal pubVal orbit i) :=
  matches_curSel_of b (envNew_selector A hn nodes hnodes b chalVal pubVal orbit i)

include hnodes in
theorem matches_old (i : Fin R.problem.cfg.compRows) :
    Matches (curSel (sIdx i)) (srcOld A hn nodes b chalVal pubVal orbit i) :=
  matches_curSel_of b (envOld_selector A hn nodes hnodes b chalVal pubVal orbit i)

include hnodes in
/-- **The decoded new and deployed canonical rows agree off `diffAt`.** -/
theorem src_agree (i : Fin R.problem.cfg.compRows) :
    ∀ k j, diffAt (sIdx i) k j = false →
      varVal (srcNew A hn nodes b chalVal pubVal orbit i) k j =
        varVal (srcOld A hn nodes b chalVal pubVal orbit i) k j := by
  intro k j hd
  have hst : stOfIdx (sIdx i) = stAt i := stOfIdx_stateIndex _
  cases k
  · simp only [diffAt, hst, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hd
    apply src_trace_congr
    intro c hc
    unfold physOf at hc
    apply envNew_trace_eq A hn nodes b chalVal pubVal orbit hnodes i c (by omega)
    · simp only [isResCol, decide_eq_false_iff_not]
      simp only [residualRoles, List.mem_cons, List.not_mem_nil, or_false] at hd
      omega
    · intro hh
      simp only [isHostCol, decide_eq_true_eq] at hh
      simp only [hostRolesOf, residualRoles, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
      omega
  · simp only [diffAt, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hd
    apply src_traceNext_congr
    intro c hc
    unfold physOf at hc
    apply envNew_traceNext_eq A hn nodes b chalVal pubVal orbit c (by omega)
    · simp only [isResCol, decide_eq_false_iff_not]
      simp only [residualRoles, hostKRoles, List.mem_cons, List.not_mem_nil, or_false] at hd
      omega
    · simp only [isHostCol, decide_eq_false_iff_not]
      simp only [residualRoles, hostKRoles, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
      omega
  · exact src_chal_eq b rfl j
  · exact src_pub_eq b rfl j

include hnodes in
/-- **Transfer of an untouched core gate.** -/
theorem core_untouched_eval (i : Fin R.problem.cfg.compRows) (g : CorrectedCoreExtGateId)
    (h74 : g.val ≠ 74) (h75 : g.val ≠ 75) (h76 : g.val ≠ 76) (h77 : g.val ≠ 77) :
    (correctedFinalExtGate g).eval
        (gather309 b (envNew A hn nodes b chalVal pubVal orbit (nodes i))).base =
      (correctedFinalExtGate g).eval
        (gatherCorrectedFinalTypedEnv b (envOld A hn nodes b chalVal pubVal orbit (nodes i))) := by
  have hb : gatherCorrectedFinalTypedEnv b (envOld A hn nodes b chalVal pubVal orbit (nodes i)) =
      (gather309 b (envOld A hn nodes b chalVal pubVal orbit (nodes i))).base := rfl
  rw [hb, ← correctedFinalExtGate_eval_source, ← correctedFinalExtGate_eval_source,
    ← eval_toSourceEnv309_of_noWalkVars _ _
      (finalExtTransitionGates_noWalkVars _ (List.get_mem _ _)),
    ← eval_toSourceEnv309_of_noWalkVars _ _
      (finalExtTransitionGates_noWalkVars _ (List.get_mem _ _))]
  exact eval_eq_of_insensitive (curSel (sIdx i)) (diffAt (sIdx i)) (coreSrc g)
    (untouched_core_insensitive (sIdx i) g h74 h75 h76 h77)
    (matches_new A hn nodes hnodes b chalVal pubVal orbit i)
    (matches_old A hn nodes hnodes b chalVal pubVal orbit i)
    (src_agree A hn nodes hnodes b chalVal pubVal orbit i)

end Transfer

/-! ## 7. Further transfer facts: base-field gates, walk columns, the successor row -/

/-- Trace columns read by a base-field gate. -/
def colsOf {F : Type*} : CoeffExpr F → List ℕ
  | .const _ => []
  | .var .traceCur i => [i]
  | .var .traceNext i => [i]
  | .var _ _ => []
  | .add a b | .sub a b | .mul a b => colsOf a ++ colsOf b
  | .neg a | .pow a _ => colsOf a

theorem coeff_eval_congr {E₁ E₂ : Env F} (hc : E₁.chal = E₂.chal) (hp : E₁.pub = E₂.pub) :
    ∀ g : CoeffExpr F, (∀ c ∈ colsOf g, E₁.trace c = E₂.trace c ∧ E₁.traceNext c = E₂.traceNext c) →
      g.eval E₁ = g.eval E₂
  | .const _, _ => rfl
  | .var .traceCur i, h => (h i (by simp [colsOf])).1
  | .var .traceNext i, h => (h i (by simp [colsOf])).2
  | .var .challenge i, _ => by simp [CoeffExpr.eval, hc]
  | .var .publicVal i, _ => by simp [CoeffExpr.eval, hp]
  | .add a b, h => by
      simp only [colsOf, List.mem_append] at h
      simp only [CoeffExpr.eval, coeff_eval_congr hc hp a (fun c hc' => h c (Or.inl hc')),
        coeff_eval_congr hc hp b (fun c hc' => h c (Or.inr hc'))]
  | .sub a b, h => by
      simp only [colsOf, List.mem_append] at h
      simp only [CoeffExpr.eval, coeff_eval_congr hc hp a (fun c hc' => h c (Or.inl hc')),
        coeff_eval_congr hc hp b (fun c hc' => h c (Or.inr hc'))]
  | .mul a b, h => by
      simp only [colsOf, List.mem_append] at h
      simp only [CoeffExpr.eval, coeff_eval_congr hc hp a (fun c hc' => h c (Or.inl hc')),
        coeff_eval_congr hc hp b (fun c hc' => h c (Or.inr hc'))]
  | .neg a, h => by simp only [colsOf] at h; simp only [CoeffExpr.eval, coeff_eval_congr hc hp a h]
  | .pow a _, h => by simp only [colsOf] at h; simp only [CoeffExpr.eval, coeff_eval_congr hc hp a h]

/-- A column outside the `𝕂`-role block `13..201` and below `303`. -/
def lowCol (c : ℕ) : Prop := c < 13 ∨ (202 ≤ c ∧ c < 303)

theorem base_gates_lowCols (n : ℕ) :
    ∀ g ∈ finalBaseTransitionGates (F := F) n, ∀ c ∈ colsOf g, lowCol c := by
  intro g hg c hc
  unfold lowCol
  simp only [finalBaseTransitionGates, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ⟨j, hj, rfl⟩ | rfl | rfl | rfl | rfl
  · simp [selectorBool, bv, colsOf] at hc; omega
  · simp [selectorOneHot, selectorSum, CoeffExpr.sumList, bv, colsOf, List.range,
      List.range.loop] at hc; omega
  · simp [firstMaskBoolean, isFirstVar, bv, colsOf] at hc; omega
  · simp [lastMaskBoolean, isLastVar, bv, colsOf] at hc; omega
  · unfold endpointOverlapConsistency at hc
    split_ifs at hc <;> simp [isFirstVar, isLastVar, bv, colsOf] at hc <;> omega

theorem equality_lowCols : ∀ g ∈ finalEndpointEqualityChecks (F := F), ∀ c ∈ colsOf g, lowCol c := by
  intro g hg c hc
  unfold lowCol
  simp only [finalEndpointEqualityChecks, List.mem_append, List.mem_map, List.mem_range] at hg
  rcases hg with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;>
    simp [endpointEqualityCheck, isFirstVar, isLastVar, bv, colsOf] at hc <;> omega

theorem exp_lowCols : ∀ g ∈ computeExpGates (F := F), ∀ c ∈ colsOf g, lowCol c := by
  intro g hg c hc
  unfold lowCol
  simp only [computeExpGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · simp [expInitGate, computeExpCol, colsOf] at hc; omega
  · simp [expStepGate, computeExpCol, arityForm, List.range, List.range.loop, colsOf] at hc
    omega

section More
variable [FiniteDimensional F K]
variable (A : SampledIOSameExecutionAssignment R p)
  (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
  (hnodes : Function.Injective nodes)
  (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
  {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)

theorem low_gate_eq (g : CoeffExpr F) (hg : ∀ c ∈ colsOf g, lowCol c) (x : F) :
    g.eval (envNew A hn nodes b chalVal pubVal orbit x) =
      g.eval (envOld A hn nodes b chalVal pubVal orbit x) := by
  refine coeff_eval_congr (E₁ := envNew A hn nodes b chalVal pubVal orbit x)
    (E₂ := envOld A hn nodes b chalVal pubVal orbit x) rfl rfl g ?_
  intro c hc
  have hl := hg c hc
  unfold lowCol at hl
  have hR : isResCol c = false := by simp [isResCol]; omega
  have hH : isHostCol c = false := by simp [isHostCol]; omega
  exact ⟨envNew_trace_eq_of_not_host A hn nodes b chalVal pubVal orbit c (by omega) hR hH x,
    envNew_traceNext_eq A hn nodes b chalVal pubVal orbit c (by omega) hR hH x⟩

include hnodes in
/-- The new walk columns carry `count(i+1)` / `acc(i+1)`. -/
theorem gather309_walk (i : Fin R.problem.cfg.compRows) (j : Fin 2) :
    (gather309 b (envNew A hn nodes b chalVal pubVal orbit (nodes i))).walk j =
      walkVal309 A i j := by
  have hc : ∀ k : Fin 3, (envNew A hn nodes b chalVal pubVal orbit (nodes i)).trace (walkLimb j k) =
      coord b (walkVal309 A i j) k := by
    intro k
    have hr := walkLimb_range j k
    simp only [envNew, envOfTrace, dif_pos hr.2, correctedCanonicalFinalTrace309, hr.1, if_true,
      walkPoly]
    rw [interp_eval nodes hnodes]
    have h1 : (walkLimb j k - 303) / 3 = j := by unfold walkLimb; omega
    have h2 : (walkLimb j k - 303) % 3 = k := by unfold walkLimb; omega
    simp only [h1, h2, dif_pos j.isLt]
  simp only [gather309, hc]
  exact b.sum_repr (walkVal309 A i j)

include hnodes in
/-- The successor walk columns at a nonterminal row. -/
theorem gather309_walkNext (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i) (j : Fin 2) :
    (gather309 b (envNew A hn nodes b chalVal pubVal orbit (nodes i))).walkNext j =
      walkVal309 A ⟨(i : ℕ) + 1, hi⟩ j := by
  rw [← gather309_walk A hn nodes hnodes b chalVal pubVal orbit ⟨(i : ℕ) + 1, hi⟩ j]
  simp only [gather309, envNew, envOfTrace, hsucc]

theorem stAt_succ_idx (i : Fin R.problem.cfg.compRows) (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    stOfIdx (sIdx ⟨(i : ℕ) + 1, hi⟩) = stAt ⟨(i : ℕ) + 1, hi⟩ := stOfIdx_stateIndex _

include hnodes in
/-- **Successor-row agreement at a nonterminal row**, off `diffNext` of the successor state. -/
theorem src_agree_next (i : Fin R.problem.cfg.compRows) (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i) :
    ∀ k j, diffNext (sIdx ⟨(i : ℕ) + 1, hi⟩) k j = false →
      varVal (srcNew A hn nodes b chalVal pubVal orbit i) k j =
        varVal (srcOld A hn nodes b chalVal pubVal orbit i) k j := by
  intro k j hd
  have hst := stOfIdx_stateIndex (stAt ⟨(i : ℕ) + 1, hi⟩)
  cases k
  · simp only [diffNext, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hd
    apply src_trace_congr
    intro c hc
    unfold physOf at hc
    apply envNew_trace_eq_of_not_host A hn nodes b chalVal pubVal orbit c (by omega)
    · simp only [isResCol, decide_eq_false_iff_not]
      simp only [residualRoles, hostKRoles, List.mem_cons, List.not_mem_nil, or_false] at hd
      omega
    · simp only [isHostCol, decide_eq_false_iff_not]
      simp only [residualRoles, hostKRoles, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
      omega
  · simp only [diffNext, hst, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hd
    apply src_traceNext_congr
    intro c hc
    unfold physOf at hc
    have h := envNew_trace_eq A hn nodes b chalVal pubVal orbit hnodes ⟨(i : ℕ) + 1, hi⟩ c
      (by omega)
      (by simp only [isResCol, decide_eq_false_iff_not]
          simp only [residualRoles, List.mem_cons, List.not_mem_nil, or_false] at hd
          omega)
      (by intro hh
          simp only [isHostCol, decide_eq_true_eq] at hh
          simp only [hostRolesOf, residualRoles, List.mem_cons, List.not_mem_nil,
            or_false] at hd ⊢
          omega)
    simp only [envNew, envOld, envOfTrace] at h ⊢
    rw [← hsucc]
    exact h
  · exact src_chal_eq b rfl j
  · exact src_pub_eq b rfl j

include hnodes in
theorem matches_next_new (i : Fin R.problem.cfg.compRows) (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i) :
    Matches (nextSel (sIdx ⟨(i : ℕ) + 1, hi⟩))
      (srcNew A hn nodes b chalVal pubVal orbit i) := by
  intro k j v hσ
  cases k <;> simp only [nextSel, reduceCtorEq] at hσ
  by_cases hj : j < 11
  · simp only [hj, if_true, Option.some.injEq] at hσ
    subst hσ
    have hs := envNew_selector A hn nodes hnodes b chalVal pubVal orbit ⟨(i : ℕ) + 1, hi⟩ j hj
    have h13 : j < 13 := by omega
    simp only [varVal, Env309.toSourceEnv, gather309, CorrectedFinalTypedEnv.toSourceEnv,
      gatherCorrectedFinalTypedEnv, show j ≠ 303 by omega, show j ≠ 306 by omega, if_false,
      dif_pos h13]
    simp only [envNew, envOfTrace] at hs ⊢
    rw [← hsucc, hs]
    split_ifs <;> simp
  · simp [hj] at hσ

include hnodes in
theorem matches_next_old (i : Fin R.problem.cfg.compRows) (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i) :
    Matches (nextSel (sIdx ⟨(i : ℕ) + 1, hi⟩))
      (srcOld A hn nodes b chalVal pubVal orbit i) := by
  intro k j v hσ
  cases k <;> simp only [nextSel, reduceCtorEq] at hσ
  by_cases hj : j < 11
  · simp only [hj, if_true, Option.some.injEq] at hσ
    subst hσ
    have hs := envOld_selector A hn nodes hnodes b chalVal pubVal orbit ⟨(i : ℕ) + 1, hi⟩ j hj
    have h13 : j < 13 := by omega
    simp only [varVal, Env309.toSourceEnv, gather309, CorrectedFinalTypedEnv.toSourceEnv,
      gatherCorrectedFinalTypedEnv, show j ≠ 303 by omega, show j ≠ 306 by omega, if_false,
      dif_pos h13]
    simp only [envOld, envOfTrace] at hs ⊢
    rw [← hsucc, hs]
    split_ifs <;> simp
  · simp [hj] at hσ

theorem matches_noSel {E : Env K} : Matches noSel E := by
  intro k i v h; simp [noSel] at h

end More

/-! ## 8. The retargeted sources against the deployed hosted ones -/

/-- A next-row overlay coordinate is the current-row one on the shifted environment. -/
theorem overlayCoord_next_eval (E : Env K) (c : ℕ) :
    (overlayCoord .traceNext c).eval E =
      (overlayCoord .traceCur c).eval ⟨E.traceNext, E.traceNext, E.chal, E.pub⟩ := by
  unfold overlayCoord
  split_ifs <;> simp [Nock.Reified.allStates, Expr.eval, pubFP]

theorem overlayCoord_cur_reads (c : Fin 5) :
    ∀ q ∈ readsE (overlayCoord .traceCur c), q.1 = .traceCur := by
  fin_cases c <;> decide

theorem eval_of_traceCur_reads {e : Expr} (he : ∀ q ∈ readsE e, q.1 = .traceCur)
    {E₁ E₂ : Env K} (ht : E₁.trace = E₂.trace) : e.eval E₁ = e.eval E₂ := by
  apply eval_congr_reads
  intro q hq
  have := he q hq
  obtain ⟨k, j⟩ := q
  simp only at this; subst this
  simp [varVal, ht]

section Walk
variable [FiniteDimensional F K]
variable (A : SampledIOSameExecutionAssignment R p)
  (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
  (hnodes : Function.Injective nodes)
  (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
  {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)

include hnodes in
/-- The deployed current overlay on the decoded canonical row. -/
theorem old_overlay_cur (i : Fin R.problem.cfg.compRows) (c : Fin 5) :
    (overlayCoord .traceCur c).eval (srcOld A hn nodes b chalVal pubVal orbit i) =
      (overlayCoord .traceCur c).eval (gatherCorrectedFinalTypedEnv b
        (envOld A hn nodes b chalVal pubVal orbit (nodes i))).toSourceEnv := by
  have := eval_toSourceEnv309_of_noWalkVars
    (gather309 b (envOld A hn nodes b chalVal pubVal orbit (nodes i)))
    (overlayCoord .traceCur c) (by fin_cases c <;> decide)
  exact this

include hnodes in
/-- The deployed successor overlay at a nonterminal row is the successor's current overlay. -/
theorem old_overlay_next (i : Fin R.problem.cfg.compRows) (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i) (c : Fin 5) :
    (overlayCoord .traceNext c).eval (srcOld A hn nodes b chalVal pubVal orbit i) =
      (overlayCoord .traceCur c).eval (srcOld A hn nodes b chalVal pubVal orbit ⟨(i : ℕ) + 1, hi⟩) := by
  rw [overlayCoord_next_eval]
  apply eval_of_traceCur_reads (overlayCoord_cur_reads c)
  funext j
  simp only [srcOld, envOld, Env309.toSourceEnv, gather309, CorrectedFinalTypedEnv.toSourceEnv,
    gatherCorrectedFinalTypedEnv, envOfTrace, hsucc]

end Walk

/-! ## 9. Small decided facts -/

theorem diff_small : ∀ s : Fin 11, diffAt s .traceCur 11 = false ∧ diffAt s .traceCur 12 = false ∧
    diffAt s .traceCur 74 = false ∧ diffAt s .traceCur 75 = false := by decide

theorem diffNext_line : ∀ s : Fin 11, diffNext s .traceNext 74 = false := by decide

theorem coreSrc74 : coreSrc ⟨74, by omega⟩ =
    Trans.walkCountStep.subst ComputeWalkLabel.finalWalkSubstInGate := by decide
theorem coreSrc75 : coreSrc ⟨75, by omega⟩ =
    Trans.walkAccStep.subst ComputeWalkLabel.finalWalkSubstInGate := by decide

/-- Reads allowed for a residual source: no residual role, no Form R / `S` column. -/
def resOK : VarKind × ℕ → Bool
  | (.traceCur, j) | (.traceNext, j) => decide (j < 71 ∨ (73 ≤ j ∧ j < 76) ∨ j = 303 ∨ j = 306)
  | _ => true

theorem residual_reads_ok :
    (∀ q ∈ readsE walkCountStep309, resOK q = true) ∧
      (∀ q ∈ readsE walkAccStep309, resOK q = true) := by decide

theorem untouched_noWalk :
    noWalkVars finalAccAfterStep = true ∧ noWalkVars finalMaskedWalkLn1 = true ∧
      noWalkVars finalAccInit = true ∧ noWalkVars finalAccTerminal = true ∧
      noWalkVars finalLnInit = true ∧
      noWalkVars OptimizedComputeFinalTypedLowering.finalMaskedWalkCount1 = true ∧
      noWalkVars OptimizedComputeFinalTypedLowering.finalMaskedWalkOut = true ∧
      noWalkVars OptimizedComputeFinalTypedLowering.finalMaskedWalkAccInit = true := by decide

/-- No `𝕂`-role read: evaluation only through base / cert / coin / public fields. -/
def noExtT : CorrectedFinalTypedExpr → Bool
  | .extCur _ | .extNext _ => false
  | .add x y | .sub x y | .mul x y => noExtT x && noExtT y
  | .neg x | .pow x _ => noExtT x
  | _ => true

theorem typed_eval_congr_noExt {a c : CorrectedFinalTypedEnv F K}
    (hb : a.baseTrace = c.baseTrace) (hbn : a.baseTraceNext = c.baseTraceNext)
    (hch : a.chal = c.chal) (hep : a.extensionPublic = c.extensionPublic)
    (hsp : a.scalarPublic = c.scalarPublic) (hcb : a.certBase = c.certBase)
    (hce : a.certExt = c.certExt) (hex : a.expCol = c.expCol) :
    ∀ t : CorrectedFinalTypedExpr, noExtT t = true → t.eval a = t.eval c
  | .baseCur i, _ => by simp [CorrectedFinalTypedExpr.eval, hb]
  | .baseNext i, _ => by simp [CorrectedFinalTypedExpr.eval, hbn]
  | .extCur _, h => by simp [noExtT] at h
  | .extNext _, h => by simp [noExtT] at h
  | .challenge i, _ => by simp [CorrectedFinalTypedExpr.eval, hch]
  | .extensionPublic i, _ => by simp [CorrectedFinalTypedExpr.eval, hep]
  | .scalarPublic i, _ => by simp [CorrectedFinalTypedExpr.eval, hsp]
  | .const _, _ => rfl
  | .add x y, h => by
      simp only [noExtT, Bool.and_eq_true] at h
      simp only [CorrectedFinalTypedExpr.eval, typed_eval_congr_noExt hb hbn hch hep hsp hcb hce hex x h.1,
        typed_eval_congr_noExt hb hbn hch hep hsp hcb hce hex y h.2]
  | .sub x y, h => by
      simp only [noExtT, Bool.and_eq_true] at h
      simp only [CorrectedFinalTypedExpr.eval, typed_eval_congr_noExt hb hbn hch hep hsp hcb hce hex x h.1,
        typed_eval_congr_noExt hb hbn hch hep hsp hcb hce hex y h.2]
  | .mul x y, h => by
      simp only [noExtT, Bool.and_eq_true] at h
      simp only [CorrectedFinalTypedExpr.eval, typed_eval_congr_noExt hb hbn hch hep hsp hcb hce hex x h.1,
        typed_eval_congr_noExt hb hbn hch hep hsp hcb hce hex y h.2]
  | .neg x, h => by
      simp only [noExtT] at h
      simp only [CorrectedFinalTypedExpr.eval, typed_eval_congr_noExt hb hbn hch hep hsp hcb hce hex x h]
  | .pow x _, h => by
      simp only [noExtT] at h
      simp only [CorrectedFinalTypedExpr.eval, typed_eval_congr_noExt hb hbn hch hep hsp hcb hce hex x h]
  | .certBase i, _ => by simp [CorrectedFinalTypedExpr.eval, hcb]
  | .certExt i, _ => by simp [CorrectedFinalTypedExpr.eval, hce]
  | .lamPow d, _ => by simp [CorrectedFinalTypedExpr.eval, hch]
  | .expCur, _ => by simp [CorrectedFinalTypedExpr.eval, hex]

theorem formRLamPins_noExt : ∀ t ∈ formRLamPins, noExtT t = true := by decide

/-! ## 10. The obligations, piece by piece -/

section Pieces
variable [FiniteDimensional F K]
variable (A : SampledIOSameExecutionAssignment R p)
  (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
  (hnodes : Function.Injective nodes)
  (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
  {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)

/-- The deployed decoded row (`gatherCorrectedFinalTypedEnv`). -/
abbrev Gold (i : Fin R.problem.cfg.compRows) : CorrectedFinalTypedEnv F K :=
  gatherCorrectedFinalTypedEnv b (envOld A hn nodes b chalVal pubVal orbit (nodes i))
/-- The new decoded row. -/
abbrev Gnew (i : Fin R.problem.cfg.compRows) : Env309 F K :=
  gather309 b (envNew A hn nodes b chalVal pubVal orbit (nodes i))

theorem srcOld_eq (i : Fin R.problem.cfg.compRows) (e : Expr) (he : noWalkVars e = true) :
    e.eval (srcOld A hn nodes b chalVal pubVal orbit i) =
      e.eval (Gold A hn nodes b chalVal pubVal orbit i).toSourceEnv :=
  eval_toSourceEnv309_of_noWalkVars _ e he

theorem srcNew_base_eq (i : Fin R.problem.cfg.compRows) (e : Expr) (he : noWalkVars e = true) :
    e.eval (srcNew A hn nodes b chalVal pubVal orbit i) =
      e.eval (Gnew A hn nodes b chalVal pubVal orbit i).base.toSourceEnv :=
  eval_toSourceEnv309_of_noWalkVars _ e he

include hnodes in
/-- An untouched source evaluates identically on the two decoded rows. -/
theorem untouched_expr_eq (i : Fin R.problem.cfg.compRows) (e : Expr) (he : noWalkVars e = true)
    (hins : Insensitive (curSel (sIdx i)) (diffAt (sIdx i)) e = true) :
    e.eval (Gnew A hn nodes b chalVal pubVal orbit i).base.toSourceEnv =
      e.eval (Gold A hn nodes b chalVal pubVal orbit i).toSourceEnv := by
  rw [← srcNew_base_eq A hn nodes b chalVal pubVal orbit i e he,
    ← srcOld_eq A hn nodes b chalVal pubVal orbit i e he]
  exact eval_eq_of_insensitive _ _ e hins (matches_new A hn nodes hnodes b chalVal pubVal orbit i)
    (matches_old A hn nodes hnodes b chalVal pubVal orbit i)
    (src_agree A hn nodes hnodes b chalVal pubVal orbit i)

theorem base_trace_eq (i : Fin R.problem.cfg.compRows) (j : Fin 13) :
    (Gnew A hn nodes b chalVal pubVal orbit i).base.baseTrace j =
      (Gold A hn nodes b chalVal pubVal orbit i).baseTrace j :=
  envNew_trace_eq_of_not_host A hn nodes b chalVal pubVal orbit j (by omega)
    (by simp [isResCol]) (by simp [isHostCol]) _

theorem ext_eq_of_plain (i : Fin R.problem.cfg.compRows) (r : Fin 63)
    (hr : (r : ℕ) ∉ hostKRoles ∧ (r : ℕ) ≠ 58 ∧ (r : ℕ) ≠ 59) :
    (Gnew A hn nodes b chalVal pubVal orbit i).base.extTrace r =
        (Gold A hn nodes b chalVal pubVal orbit i).extTrace r ∧
      (Gnew A hn nodes b chalVal pubVal orbit i).base.extTraceNext r =
        (Gold A hn nodes b chalVal pubVal orbit i).extTraceNext r := by
  have hcols : ∀ k : Fin 3, isResCol (correctedFinalExtCoordIndex r k) = false ∧
      isHostCol (correctedFinalExtCoordIndex r k) = false := by
    intro k
    simp only [hostKRoles, List.mem_cons, List.not_mem_nil, or_false] at hr
    have := r.isLt; have := k.isLt
    simp only [isResCol, isHostCol, correctedFinalExtCoordIndex, hostKRoles, List.mem_cons,
      List.not_mem_nil, or_false, decide_eq_false_iff_not]
    constructor
    · exact decide_eq_false (by omega)
    · omega
  constructor
  · simp only [Gnew, Gold, gather309, gatherCorrectedFinalTypedEnv]
    apply Finset.sum_congr rfl; intro k _
    rw [envNew_trace_eq_of_not_host A hn nodes b chalVal pubVal orbit _
      (by simp [correctedFinalExtCoordIndex]; omega) (hcols k).1 (hcols k).2]
  · simp only [Gnew, Gold, gather309, gatherCorrectedFinalTypedEnv]
    apply Finset.sum_congr rfl; intro k _
    rw [envNew_traceNext_eq A hn nodes b chalVal pubVal orbit _
      (by simp [correctedFinalExtCoordIndex]; omega) (hcols k).1 (hcols k).2]

include hnodes in
/-- Untouched core positions carry the deployed semantic value. -/
theorem coreSem_untouched (i : Fin R.problem.cfg.compRows) (g : CorrectedCoreExtGateId)
    (h74 : g.val ≠ 74) (h75 : g.val ≠ 75) (h76 : g.val ≠ 76) (h77 : g.val ≠ 77) :
    coreSemValue309 (Gnew A hn nodes b chalVal pubVal orbit i) g =
      correctedCoreSemanticValue (Gold A hn nodes b chalVal pubVal orbit i) g := by
  have h76' : g ≠ packedQueueNonEmptyId := fun h => h76 (by rw [h])
  have h77' : g ≠ packedQueueTilingId := fun h => h77 (by rw [h])
  have h74' : g ≠ packedWalkCountId := fun h => h74 (by rw [h])
  have h75' : g ≠ packedWalkAccId := fun h => h75 (by rw [h])
  have hb12 := base_trace_eq A hn nodes b chalVal pubVal orbit i 12
  have hgate := core_untouched_eval A hn nodes hnodes b chalVal pubVal orbit i g h74 h75 h76 h77
  simp only [coreSemValue309, h76', h77', if_false, correctedCoreSemanticValue, h74', h75']
  split_ifs with h81 h7273
  · have he60 := (ext_eq_of_plain A hn nodes b chalVal pubVal orbit i 60
      ⟨by decide, by decide, by decide⟩).1
    have he32 := (ext_eq_of_plain A hn nodes b chalVal pubVal orbit i 32
      ⟨by decide, by decide, by decide⟩).2
    simp only [accAfterChain, CorrectedFinalTypedExpr.eval]
    rw [hb12, he60, he32]
  · simp only [notLastScalar, hb12, hgate]
  · exact hgate

include hnodes in
/-- The queue gates at 309 equal the deployed hosted ones on the deployed row. -/
theorem queue_eq (i : Fin R.problem.cfg.compRows) :
    queueNonEmpty309.eval (Gnew A hn nodes b chalVal pubVal orbit i) =
        (correctedFinalExtGate packedQueueNonEmptyId).eval (Gold A hn nodes b chalVal pubVal orbit i) ∧
      queueTiling309.eval (Gnew A hn nodes b chalVal pubVal orbit i) =
        (correctedFinalExtGate packedQueueTilingId).eval (Gold A hn nodes b chalVal pubVal orbit i) := by
  have hs := diff_small (sIdx i)
  have hag := src_agree A hn nodes hnodes b chalVal pubVal orbit i
  have h12 := hag .traceCur 12 hs.2.1
  have h74 := hag .traceCur 74 hs.2.2.1
  have h75 := hag .traceCur 75 hs.2.2.2
  have hw : (srcNew A hn nodes b chalVal pubVal orbit i).trace 303 =
      A.exact.computeWalk.count ((i : ℕ) + 1) := by
    show (Gnew A hn nodes b chalVal pubVal orbit i).walk 0 = _
    rw [gather309_walk A hn nodes hnodes b chalVal pubVal orbit i 0]; rfl
  have hov := canonical_gather_walkOverlay_current A hn nodes hnodes b chalVal pubVal orbit i 0
  norm_num at hov
  simp only [varVal] at h12 h74 h75
  constructor
  · rw [show queueNonEmpty309 = lowerW walkQueueNonEmpty309 from rfl, ← lower309_eval _ _ _ (lower309_some _ lower309_total.2.2.1),
      ← correctedFinalExtGate_eval_source]
    change walkQueueNonEmpty309.eval (srcNew A hn nodes b chalVal pubVal orbit i) =
      (finalExtTransitionGates.get ⟨76, by simp⟩).eval _
    rw [packedQueueNonEmpty_source]
    simp only [walkQueueNonEmpty309, walkQueueNonEmpty, Expr.eval, walkInv, walkInvIndex,
      walkInvRole, ext0, finalWalkLine, finalWalkLineIndex, finalWalkLineRole, walkCountCol]
    rw [hw, ← hov, h12, h74, h75]
    simp only [srcOld, Env309.toSourceEnv, gather309]
    norm_num
  · rw [show queueTiling309 = lowerW walkQueueTiling309 from rfl,
      ← lower309_eval _ _ _ (lower309_some _ lower309_total.2.2.2.1),
      ← correctedFinalExtGate_eval_source]
    change walkQueueTiling309.eval (srcNew A hn nodes b chalVal pubVal orbit i) =
      (finalExtTransitionGates.get ⟨77, by simp⟩).eval _
    rw [packedQueueTiling_source]
    simp only [walkQueueTiling309, walkQueueTiling, Expr.eval, ext0, finalWalkLine,
      finalWalkLineIndex, finalWalkLineRole, walkCountCol]
    rw [hw, ← hov, h12, h74]
    simp only [srcOld, Env309.toSourceEnv, gather309]
    norm_num

end Pieces

/-! ## 11. The residual pins and the walk recurrences -/

section Residual
variable [FiniteDimensional F K]
variable (A : SampledIOSameExecutionAssignment R p)
  (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
  (hnodes : Function.Injective nodes)
  (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
  {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)

include hnodes in
theorem residual_cell (i : Fin R.problem.cfg.compRows) (j : Fin 2) (k : Fin 3) :
    (envNew A hn nodes b chalVal pubVal orbit (nodes i)).trace (13 + 3 * (58 + (j : ℕ)) + k) =
      (compile309 b (residualSource309 j) k).eval
        (envNewPre A hn nodes b chalVal pubVal orbit (nodes i)) := by
  have hj := j.isLt; have hk := k.isLt
  have hW : ¬ 303 ≤ 13 + 3 * (58 + (j : ℕ)) + k := by omega
  have hH : isHostCol (13 + 3 * (58 + (j : ℕ)) + k) = false := by
    simp [isHostCol, hostKRoles]; omega
  have hres : isResCol (13 + 3 * (58 + (j : ℕ)) + k) = true := by
    simp [isResCol]; omega
  simp only [envNew, envOfTrace, dif_pos (show 13 + 3 * (58 + (j : ℕ)) + k < 309 by omega),
    correctedCanonicalFinalTrace309, hW, if_false, hH, Bool.false_eq_true]
  rw [dif_pos hres]
  simp only [residualPoly309]
  rw [interp_eval nodes hnodes]
  have e1 : (⟨(13 + 3 * (58 + (j : ℕ)) + k - 13) / 3 - 58, by omega⟩ : Fin 2) = j :=
    Fin.ext (by simp; omega)
  have e2 : (⟨(13 + 3 * (58 + (j : ℕ)) + k - 13) % 3, by omega⟩ : Fin 3) = k :=
    Fin.ext (by simp; omega)
  rw [e1, e2]
  rfl

/-- Reads allowed by `resOK` agree between the final and preliminary 309 rows. -/
theorem src_new_pre_agree (i : Fin R.problem.cfg.compRows) :
    ∀ q : VarKind × ℕ, resOK q = true →
      varVal (gather309 b (envNew A hn nodes b chalVal pubVal orbit (nodes i))).toSourceEnv q.1 q.2 =
        varVal (gather309 b (envNewPre A hn nodes b chalVal pubVal orbit (nodes i))).toSourceEnv q.1 q.2 := by
  rintro ⟨k, j⟩ hq
  cases k
  · simp only [resOK, decide_eq_true_eq] at hq
    apply src_trace_congr
    intro c hc
    unfold physOf at hc
    exact (envNew_eq_pre A hn nodes b chalVal pubVal orbit c (by omega)
      (by simp [isResCol]; omega) _).1
  · simp only [resOK, decide_eq_true_eq] at hq
    apply src_traceNext_congr
    intro c hc
    unfold physOf at hc
    exact (envNew_eq_pre A hn nodes b chalVal pubVal orbit c (by omega)
      (by simp [isResCol]; omega) _).2
  · exact src_chal_eq b rfl j
  · exact src_pub_eq b rfl j

include hnodes in
/-- **The residual pin**: the residual role carries the retargeted walk recurrence. -/
theorem residual_identity (i : Fin R.problem.cfg.compRows) (j : Fin 2) :
    (Gnew A hn nodes b chalVal pubVal orbit i).base.extTrace ⟨58 + (j : ℕ), by omega⟩ =
      (residualSource309 j).eval (Gnew A hn nodes b chalVal pubVal orbit i) := by
  have hsum : (Gnew A hn nodes b chalVal pubVal orbit i).base.extTrace ⟨58 + (j : ℕ), by omega⟩ =
      (residualSource309 j).eval
        (gather309 b (envNewPre A hn nodes b chalVal pubVal orbit (nodes i))) := by
    simp only [Gnew, gather309, gatherCorrectedFinalTypedEnv, correctedFinalExtCoordIndex]
    have hc : ∀ k : Fin 3,
        (envNew A hn nodes b chalVal pubVal orbit (nodes i)).trace (13 + 3 * (58 + (j : ℕ)) + k) =
          coord b ((residualSource309 j).eval
            (gather309 b (envNewPre A hn nodes b chalVal pubVal orbit (nodes i)))) k := by
      intro k
      rw [residual_cell A hn nodes hnodes b chalVal pubVal orbit i j k,
        compile309_eval b _ _ (isCoordEnv309_gather b _)]
    simp only [hc]
    exact b.sum_repr _
  rw [hsum]
  have hl : ∀ e, (lower309 e).isSome → (∀ q ∈ readsE e, resOK q = true) →
      (lowerW e).eval (gather309 b (envNewPre A hn nodes b chalVal pubVal orbit (nodes i))) =
        (lowerW e).eval (Gnew A hn nodes b chalVal pubVal orbit i) := by
    intro e hs hr
    rw [← lower309_eval _ _ _ (lower309_some e hs), ← lower309_eval _ _ _ (lower309_some e hs)]
    symm
    apply eval_congr_reads
    intro q hq
    exact src_new_pre_agree A hn nodes b chalVal pubVal orbit i q (hr q hq)
  fin_cases j
  · exact hl _ lower309_total.1 residual_reads_ok.1
  · exact hl _ lower309_total.2.1 residual_reads_ok.2

include hnodes in
/-- **The walk recurrences at 309 are the deployed hosted ones** at a nonterminal row. -/
theorem walk_steps_eq (i : Fin R.problem.cfg.compRows) (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i) :
    walkCountStep309.eval (srcNew A hn nodes b chalVal pubVal orbit i) =
        (coreSrc ⟨74, by omega⟩).eval (srcOld A hn nodes b chalVal pubVal orbit i) ∧
      walkAccStep309.eval (srcNew A hn nodes b chalVal pubVal orbit i) =
        (coreSrc ⟨75, by omega⟩).eval (srcOld A hn nodes b chalVal pubVal orbit i) := by
  set s' := sIdx (R := R) ⟨(i : ℕ) + 1, hi⟩
  have hag := src_agree_next A hn nodes hnodes b chalVal pubVal orbit i hi hsucc
  have hmn := matches_next_new A hn nodes hnodes b chalVal pubVal orbit i hi hsucc
  have hmo := matches_next_old A hn nodes hnodes b chalVal pubVal orbit i hi hsucc
  have hrec := next_labels_insensitive s'
  have hcm := eval_eq_of_insensitive _ _ _ hrec.2.2 matches_noSel matches_noSel hag
  have hlab := eval_eq_of_insensitive _ _ _ hrec.1 hmn hmo hag
  have hcc := eval_eq_of_insensitive _ _ _ hrec.2.1 hmn hmo hag
  have hln : (srcNew A hn nodes b chalVal pubVal orbit i).traceNext 74 =
      (srcOld A hn nodes b chalVal pubVal orbit i).traceNext 74 :=
    hag .traceNext 74 (diffNext_line s')
  -- walk columns
  have hW (j : Fin 2) : (srcNew A hn nodes b chalVal pubVal orbit i).trace (303 + 3 * (j : ℕ)) =
      walkVal309 A i j := by
    rw [← gather309_walk A hn nodes hnodes b chalVal pubVal orbit i j]
    fin_cases j <;> rfl
  have hWn (j : Fin 2) : (srcNew A hn nodes b chalVal pubVal orbit i).traceNext (303 + 3 * (j : ℕ)) =
      walkVal309 A ⟨(i : ℕ) + 1, hi⟩ j := by
    rw [← gather309_walkNext A hn nodes hnodes b chalVal pubVal orbit i hi hsucc j]
    fin_cases j <;> rfl
  -- the deployed overlays
  have hoc (c : Fin 5) := (old_overlay_cur A hn nodes hnodes b chalVal pubVal orbit i c).trans
    (canonical_gather_walkOverlay_current A hn nodes hnodes b chalVal pubVal orbit i c)
  have hon (c : Fin 5) := (old_overlay_next A hn nodes hnodes b chalVal pubVal orbit i hi hsucc c).trans
    ((old_overlay_cur A hn nodes hnodes b chalVal pubVal orbit ⟨(i : ℕ) + 1, hi⟩ c).trans
      (canonical_gather_walkOverlay_current A hn nodes hnodes b chalVal pubVal orbit
        ⟨(i : ℕ) + 1, hi⟩ c))
  have hc0 := hoc 0; have hc1 := hoc 1; have hn0 := hon 0; have hn1 := hon 1
  norm_num at hc0 hc1 hn0 hn1
  have hW0 := hW 0; have hW1 := hW 1; have hWn0 := hWn 0; have hWn1 := hWn 1
  simp only [walkVal309] at hW0 hW1 hWn0 hWn1
  norm_num at hW0 hW1 hWn0 hWn1
  constructor
  · rw [coreSrc74]
    simp only [walkCountStep309, Expr.eval_subst, Trans.walkCountStep, Expr.eval, Env.ofSubst,
      Trans.tn, tc, finalWalkSubstInGate309, ComputeWalkLabel.finalWalkSubstInGate, walkCountCol]
    rw [hW0, hWn0, hc0, hn0, hcm]
  · rw [coreSrc75]
    simp only [walkAccStep309, Expr.eval_subst, Trans.walkAccStep, Expr.eval, Env.ofSubst,
      Trans.tn, tc, finalWalkSubstInGate309, ComputeWalkLabel.finalWalkSubstInGate, walkCountCol,
      walkAccCol, finalWalkLine, finalWalkLineIndex, finalWalkLineRole, ext0]
    rw [hW0, hW1, hWn1, hc0, hc1, hn1, hlab, hcc, hln]

end Residual

/-! ## 12. The walk endpoints -/

section Endpoints
variable [FiniteDimensional F K]
variable (A : SampledIOSameExecutionAssignment R p)
  (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
  (hnodes : Function.Injective nodes)
  (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
  {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)

include hnodes in
theorem srcOld_mask (i : Fin R.problem.cfg.compRows) :
    (srcOld A hn nodes b chalVal pubVal orbit i).trace 11 =
        (if (i : ℕ) = 0 then 1 else 0) ∧
      (srcOld A hn nodes b chalVal pubVal orbit i).trace 12 =
        (if i = ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩ then 1 else 0) := by
  have h11 := canonical_gather_base_current A hn nodes hnodes b chalVal pubVal orbit i 11
  have h12 := canonical_gather_base_current A hn nodes hnodes b chalVal pubVal orbit i 12
  simp only [srcOld, Env309.toSourceEnv, gather309, CorrectedFinalTypedEnv.toSourceEnv]
  simp only [gatherCorrectedFinalTypedEnv] at h11 h12
  constructor
  · simp only [show (11 : ℕ) ≠ 303 by omega, show (11 : ℕ) ≠ 306 by omega, if_false,
      dif_pos (show (11 : ℕ) < 13 by omega)]
    have : (envOld A hn nodes b chalVal pubVal orbit (nodes i)).trace 11 = finalBaseCell A hn i 11 :=
      by simpa using h11
    change algebraMap F K ((envOld A hn nodes b chalVal pubVal orbit (nodes i)).trace 11) = _
    rw [this]; simp [finalBaseCell]
  · simp only [show (12 : ℕ) ≠ 303 by omega, show (12 : ℕ) ≠ 306 by omega, if_false,
      dif_pos (show (12 : ℕ) < 13 by omega)]
    have : (envOld A hn nodes b chalVal pubVal orbit (nodes i)).trace 12 = finalBaseCell A hn i 12 :=
      by simpa using h12
    change algebraMap F K ((envOld A hn nodes b chalVal pubVal orbit (nodes i)).trace 12) = _
    rw [this]; simp [finalBaseCell]

include hnodes in
theorem matches_first (hpub : ExactFinalPublicCoordinates b R hn pubVal) :
    Matches (firstSel (sIdx (R := R) ⟨0, hn⟩)) (srcNew A hn nodes b chalVal pubVal orbit ⟨0, hn⟩) ∧
      Matches (firstSel (sIdx (R := R) ⟨0, hn⟩)) (srcOld A hn nodes b chalVal pubVal orbit ⟨0, hn⟩) := by
  have hcur := matches_new A hn nodes hnodes b chalVal pubVal orbit ⟨0, hn⟩
  have hcur' := matches_old A hn nodes hnodes b chalVal pubVal orbit ⟨0, hn⟩
  have hpubv : ∀ E : Env F, E.pub = pubVal → ∀ j v, firstSel (sIdx (R := R) ⟨0, hn⟩) .publicVal j = some v →
      varVal (gather309 b E).toSourceEnv .publicVal j = (v : K) := by
    intro E hE j v hσ
    simp only [firstSel] at hσ
    by_cases hj : 20 ≤ j ∧ j < 31
    · simp only [hj, and_self, if_true, Option.some.injEq] at hσ
      subst hσ
      have hp := hpub.2.1 ⟨j - 20, by omega⟩
      have hj3 : ¬ j < 3 := by omega
      have hj42 : 20 ≤ j ∧ j < 42 := ⟨hj.1, by omega⟩
      simp only [varVal, Env309.toSourceEnv, gather309, CorrectedFinalTypedEnv.toSourceEnv,
        gatherCorrectedFinalTypedEnv, dif_neg hj3, dif_pos hj42, hE]
      rw [show 20 + (j - 20) = j by omega] at hp
      simp only [show (20 : ℕ) + (j - 20) = j by omega, hp]
      split_ifs with h1 h2 h2 <;> simp_all [Fin.ext_iff, sIdx, stAt] <;> omega
    · simp [hj] at hσ
  constructor
  · intro k j v hσ
    cases k
    · exact hcur .traceCur j v (by simpa [firstSel, curSel] using hσ)
    · simp [firstSel] at hσ
    · simp [firstSel] at hσ
    · exact hpubv _ rfl j v hσ
  · intro k j v hσ
    cases k
    · exact hcur' .traceCur j v (by simpa [firstSel, curSel] using hσ)
    · simp [firstSel] at hσ
    · simp [firstSel] at hσ
    · exact hpubv _ rfl j v hσ

include hnodes in
/-- The masked-walk endpoints at 309 equal the deployed ones on the deployed row. -/
theorem endpoints_eq (hpub : ExactFinalPublicCoordinates b R hn pubVal)
    (i : Fin R.problem.cfg.compRows) :
    finalMaskedWalkCount1_309.eval (srcNew A hn nodes b chalVal pubVal orbit i) =
        OptimizedComputeFinalTypedLowering.finalMaskedWalkCount1.eval
          (srcOld A hn nodes b chalVal pubVal orbit i) ∧
      finalMaskedWalkOut309.eval (srcNew A hn nodes b chalVal pubVal orbit i) =
        OptimizedComputeFinalTypedLowering.finalMaskedWalkOut.eval
          (srcOld A hn nodes b chalVal pubVal orbit i) ∧
      finalMaskedWalkAccInit309.eval (srcNew A hn nodes b chalVal pubVal orbit i) =
        OptimizedComputeFinalTypedLowering.finalMaskedWalkAccInit.eval
          (srcOld A hn nodes b chalVal pubVal orbit i) := by
  have hs := diff_small (sIdx i)
  have hag := src_agree A hn nodes hnodes b chalVal pubVal orbit i
  have h11 : (srcNew A hn nodes b chalVal pubVal orbit i).trace 11 =
      (srcOld A hn nodes b chalVal pubVal orbit i).trace 11 := hag .traceCur 11 hs.1
  have h12 : (srcNew A hn nodes b chalVal pubVal orbit i).trace 12 =
      (srcOld A hn nodes b chalVal pubVal orbit i).trace 12 := hag .traceCur 12 hs.2.1
  have h74 : (srcNew A hn nodes b chalVal pubVal orbit i).trace 74 =
      (srcOld A hn nodes b chalVal pubVal orbit i).trace 74 := hag .traceCur 74 hs.2.2.1
  have hp (j : ℕ) : (srcNew A hn nodes b chalVal pubVal orbit i).pub j =
      (srcOld A hn nodes b chalVal pubVal orbit i).pub j := src_pub_eq b rfl j
  have hmask := srcOld_mask A hn nodes hnodes b chalVal pubVal orbit i
  have hcmF := eval_eq_of_insensitive _ _ _ (first_labels_insensitive (sIdx i)).2.2
    matches_noSel matches_noSel hag
  have hW (j : Fin 2) : (srcNew A hn nodes b chalVal pubVal orbit i).trace (303 + 3 * (j : ℕ)) =
      walkVal309 A i j := by
    rw [← gather309_walk A hn nodes hnodes b chalVal pubVal orbit i j]
    fin_cases j <;> rfl
  have hW0 := hW 0; have hW1 := hW 1
  simp only [walkVal309] at hW0 hW1
  norm_num at hW0 hW1
  have hov (c : Fin 5) := (old_overlay_cur A hn nodes hnodes b chalVal pubVal orbit i c).trans
    (canonical_gather_walkOverlay_current A hn nodes hnodes b chalVal pubVal orbit i c)
  have hov0 := hov 0; have hov1 := hov 1
  norm_num at hov0 hov1
  refine ⟨?_, ?_, ?_⟩
  · simp only [finalMaskedWalkCount1_309, OptimizedComputeFinalTypedLowering.finalMaskedWalkCount1,
      finalOptimizedWalkCount1, Expr.eval, Expr.eval_subst, Trans.walkCount1, Env.ofSubst, tc,
      Trans.pubv, finalWalkInitialSubst309, finalWalkInitialSubst, fixedIsFirst, walkCountCol]
    rw [h11, hp 0, hcmF]
    by_cases hi0 : (i : ℕ) = 0
    · have hio := canonical_initialOverlayCoord_first A hn nodes hnodes b chalVal pubVal orbit hpub 0
      have hi : i = ⟨0, hn⟩ := Fin.ext hi0
      subst hi
      rw [srcOld_eq A hn nodes b chalVal pubVal orbit _ (initialOverlayCoord 0) (by decide)]
      norm_num at hio
      have hc := canonical_gather_walkOverlay_current A hn nodes hnodes b chalVal pubVal orbit
        ⟨0, hn⟩ 0
      norm_num at hc
      rw [hio, hc, hW0]
    · rw [hmask.1, if_neg hi0]; simp
  · simp only [finalMaskedWalkOut309, OptimizedComputeFinalTypedLowering.finalMaskedWalkOut,
      finalOptimizedWalkOut, Expr.eval, Expr.eval_subst, Trans.walkOut, Env.ofSubst, tc,
      finalWalkTerminalSubst309, finalWalkTerminalSubst, fixedIsLast, walkAccCol]
    rw [h12]
    by_cases hil : i = ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩
    · have hio := canonical_terminalOverlayCoord_last A hn nodes hnodes b chalVal pubVal orbit hpub 1
      subst hil
      rw [srcOld_eq A hn nodes b chalVal pubVal orbit _ (terminalOverlayCoord 1) (by decide)]
      norm_num at hio
      have hc := canonical_gather_walkOverlay_current A hn nodes hnodes b chalVal pubVal orbit
        ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩ 1
      norm_num at hc
      rw [hio, hc, hW1]
    · rw [hmask.2, if_neg hil]; simp
  · simp only [finalMaskedWalkAccInit309, OptimizedComputeFinalTypedLowering.finalMaskedWalkAccInit,
      finalOptimizedWalkAccInit, Expr.eval, Expr.eval_subst, Trans.walkAccInit, Env.ofSubst, tc,
      Trans.pubv, finalWalkInitialSubst309, finalWalkInitialSubst, fixedIsFirst, walkAccCol,
      finalWalkLine, finalWalkLineIndex, finalWalkLineRole, ext0]
    rw [h11, hp 0, hp 1, h74]
    by_cases hi0 : (i : ℕ) = 0
    · have hio := canonical_initialOverlayCoord_first A hn nodes hnodes b chalVal pubVal orbit hpub 1
      have hi : i = ⟨0, hn⟩ := Fin.ext hi0
      subst hi
      have hm := matches_first A hn nodes hnodes b chalVal pubVal orbit hpub
      have hlab := eval_eq_of_insensitive _ _ _ (first_labels_insensitive (sIdx (R := R) ⟨0, hn⟩)).1
        hm.1 hm.2 hag
      have hcc := eval_eq_of_insensitive _ _ _ (first_labels_insensitive (sIdx (R := R) ⟨0, hn⟩)).2.1
        hm.1 hm.2 hag
      rw [hlab, hcc, srcOld_eq A hn nodes b chalVal pubVal orbit _ (initialOverlayCoord 1) (by decide)]
      norm_num at hio
      have hc := canonical_gather_walkOverlay_current A hn nodes hnodes b chalVal pubVal orbit
        ⟨0, hn⟩ 1
      norm_num at hc
      rw [hio, hc, hW1]
    · rw [hmask.1, if_neg hi0]; simp

end Endpoints

/-! ## 13. Base-field gates read no host / residual / walk column -/

/-- A physical column that is identical on the two canonical traces. -/
def plainCol (c : ℕ) : Prop := c < 303 ∧ isHostCol c = false ∧ isResCol c = false

/-- Every column the gate reads is plain. -/
def Good (g : CoeffExpr F) : Prop := ∀ c ∈ colsOf g, plainCol c

section GoodLemmas
open OptimizedComputeRangeCertificate

theorem plainCol_of (c : ℕ) (h : c < 13 ∨ (202 ≤ c ∧ c < 303)) : plainCol c := by
  refine ⟨by omega, ?_, ?_⟩ <;> simp [isHostCol, isResCol] <;> omega

theorem good_const (x : F) : Good (.const x) := by intro c hc; simp [colsOf] at hc
theorem good_bcur (i : ℕ) (h : plainCol i) : Good (bcur (F := F) i) := by
  intro c hc; simp [bcur, colsOf] at hc; subst hc; exact h
theorem good_add {a b : CoeffExpr F} (ha : Good a) (hb : Good b) : Good (.add a b) := by
  intro c hc; simp only [colsOf, List.mem_append] at hc; exact hc.elim (ha c) (hb c)
theorem good_sub {a b : CoeffExpr F} (ha : Good a) (hb : Good b) : Good (.sub a b) := by
  intro c hc; simp only [colsOf, List.mem_append] at hc; exact hc.elim (ha c) (hb c)
theorem good_mul {a b : CoeffExpr F} (ha : Good a) (hb : Good b) : Good (.mul a b) := by
  intro c hc; simp only [colsOf, List.mem_append] at hc; exact hc.elim (ha c) (hb c)

theorem good_cert (i : ℕ) (h1 : 202 ≤ i) (h2 : i < 303) : Good (bcur (F := F) i) :=
  good_bcur i (plainCol_of i (Or.inr ⟨h1, h2⟩))

theorem good_colC (j : ℕ) (hj : j < 63) : Good (colC (F := F) j) :=
  good_cert _ (by simp only [col0]; omega) (by simp only [col0]; omega)
theorem good_colM (k : ℕ) (hk : k < 6) : Good (colM (F := F) k) :=
  good_cert _ (by simp only [col0]; omega) (by simp only [col0]; omega)
theorem good_colE (k : ℕ) (hk : k < 21) : Good (colE (F := F) k) :=
  good_cert _ (by simp only [col0]; omega) (by simp only [col0]; omega)
theorem good_colTop : Good (colTop (F := F)) := good_cert _ (by decide) (by decide)
theorem good_colP : Good (colP (F := F)) := good_cert _ (by decide) (by decide)
theorem good_colHbase : Good (colHbase (F := F)) := good_cert _ (by decide) (by decide)
theorem good_colTbase : Good (colTbase (F := F)) := good_cert _ (by decide) (by decide)

theorem good_bbool {e : CoeffExpr F} (h : Good e) : Good (bbool e) :=
  good_mul h (good_sub h (good_const _))

theorem good_lm (k : ℕ) (hk : k < 6) : Good (lm (F := F) k) := by
  unfold lm; split
  · exact good_colM k hk
  · exact good_sub (good_const _) (good_colM k hk)

theorem good_linCol (j : ℕ) (hj : j < 63) : Good (linCol (F := F) j) := by
  unfold linCol; split
  · exact good_colC j hj
  · exact good_sub (good_const _) (good_colC j hj)

theorem good_bitCoeff (b : Bool) : Good (bitCoeff (F := F) b) := by
  unfold bitCoeff; split <;> exact good_const _

theorem good_helperAt (k : ℕ) (hk : k ≤ 21) : Good (helperAt (F := F) k) := by
  unfold helperAt; split
  · exact good_colTop
  · exact good_colE _ (by omega)

theorem good_foldMul (ls : List (CoeffExpr F)) (E : CoeffExpr F)
    (hE : Good E) (hl : ∀ l ∈ ls, Good l) : Good (foldMul ls E) := by
  induction ls generalizing E with
  | nil => simpa [foldMul] using hE
  | cons l ls ih =>
      simp only [foldMul]
      exact ih _ (good_mul hE (hl l (by simp))) (fun x hx => hl x (by simp [hx]))

theorem good_sumExpr (ls : List (CoeffExpr F)) (hl : ∀ l ∈ ls, Good l) :
    Good (sumExpr ls) := by
  induction ls with
  | nil => exact good_const _
  | cons l ls ih => exact good_add (hl l (by simp)) (ih fun x hx => hl x (by simp [hx]))

theorem good_termAt (k : ℕ) (hk : k < 63) : Good (termAt (F := F) k) := by
  unfold termAt
  refine good_mul (good_foldMul _ _ (good_helperAt _ (by omega)) ?_)
    (good_sub (good_const _) (good_colC k hk))
  intro l hl
  simp only [List.mem_map, List.mem_range] at hl
  obtain ⟨j, hj, rfl⟩ := hl
  have : k % 3 ≤ k := Nat.mod_le k 3
  exact good_linCol _ (by omega)

theorem good_eqmAt (k : ℕ) : Good (eqmAt (F := F) k) := by
  unfold eqmAt
  split
  · exact good_mul (good_mul good_colP (good_lm 2 (by decide))) (good_lm 1 (by decide))
  · exact good_mul good_colP (good_lm 2 (by decide))
  · exact good_colP
  · exact good_mul (good_lm 5 (by decide)) (good_lm 4 (by decide))
  · exact good_lm 5 (by decide)
  · exact good_const _
  · exact good_const _

theorem good_rangeTerm (k : ℕ) (hk : k < 6) : Good (rangeTerm (F := F) k) := by
  unfold rangeTerm
  refine good_mul (good_mul (good_eqmAt _) (good_sub (good_const _) (good_colM k hk))) ?_
  split <;> exact good_const _

theorem good_factor2 (k : ℕ) (hk : k < 6) : Good (factor2 (F := F) k) :=
  good_add (good_const _) (good_mul (good_colM k hk) (good_sub (good_const _) (good_const _)))

theorem good_helperPinAt (k : ℕ) (hk : k < 21) : Good (helperPinAt (F := F) k) := by
  unfold helperPinAt
  exact good_sub (good_colE k hk)
    (good_mul (good_mul (good_mul (good_helperAt k (by omega))
      (good_linCol _ (by omega))) (good_linCol _ (by omega))) (good_linCol _ (by omega)))

theorem good_csumAcc (n : ℕ) (hn : n ≤ 63) : Good (csumAcc (F := F) n) := by
  induction n with
  | zero => exact good_const _
  | succ n ih => exact good_add (ih (by omega)) (good_mul (good_colC n (by omega)) (good_const _))

theorem good_axisEquation : Good (axisEquation (F := F)) := by
  unfold axisEquation ftLeaf fthLeaf csum
  have h0 : plainCol 0 := plainCol_of 0 (by omega)
  have h9 : plainCol 9 := plainCol_of 9 (by omega)
  have h136 : plainCol 136 := ⟨by omega, by decide, by decide⟩
  have h145 : plainCol 145 := ⟨by omega, by decide, by decide⟩
  exact good_add
    (good_mul (good_bcur 0 h0) (good_sub (good_bcur 136 h136)
      (good_mul good_colTbase (good_csumAcc 63 le_rfl))))
    (good_mul (good_bcur 9 h9) (good_sub (good_bcur 145 h145)
      (good_mul good_colTbase (good_csumAcc 63 le_rfl))))

theorem formR_good : ∀ g ∈ formRCertificateGates (F := F), Good g := by
  intro g hg
  simp only [formRCertificateGates, formRNamed, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hg
  rcases hg with ((((hb | hp) | hr) | hh) | hc | hc | hc)
  · simp only [booleanGates, List.mem_append, List.mem_map, List.mem_range] at hb
    rcases hb with ⟨j, hj, rfl⟩ | ⟨k, hk, rfl⟩
    · split_ifs
      · exact good_colC j hj
      · exact good_bbool (good_colC j hj)
    · exact good_bbool (good_colM k hk)
  · simp only [powerPins, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact good_sub good_colHbase (good_mul (good_mul
        (good_factor2 0 (by decide)) (good_factor2 1 (by decide))) (good_factor2 2 (by decide)))
    · exact good_sub good_colTbase (good_mul (good_mul (good_mul
        good_colHbase (good_factor2 3 (by decide))) (good_factor2 4 (by decide)))
        (good_factor2 5 (by decide)))
  · simp only [formRPins, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact good_sub good_colP (good_mul (good_mul
        (good_lm 5 (by decide)) (good_lm 4 (by decide))) (good_lm 3 (by decide)))
    · exact good_sub good_colTop (good_mul (good_mul (good_mul
        good_colP (good_lm 2 (by decide))) (good_lm 1 (by decide))) (good_lm 0 (by decide)))
  · simp only [helperPins, List.mem_map, List.mem_range] at hh
    obtain ⟨k, hk, rfl⟩ := hh
    exact good_helperPinAt k hk
  · subst hc
    refine good_sub (good_sumExpr _ ?_) good_colTop
    intro t ht
    simp only [comparisonTerms, List.mem_map, List.mem_range] at ht
    obtain ⟨k, hk, rfl⟩ := ht
    exact good_mul (good_bitCoeff _) (good_termAt k hk)
  · subst hc
    refine good_sub (good_add (good_sumExpr _ ?_) good_colTop) (good_const _)
    intro t ht
    simp only [rangeTerms, List.mem_map, List.mem_range] at ht
    obtain ⟨k, hk, rfl⟩ := ht
    exact good_rangeTerm k hk
  · subst hc; exact good_axisEquation

theorem good_of_lowCols {g : CoeffExpr F} (h : ∀ c ∈ colsOf g, lowCol c) : Good g :=
  fun c hc => plainCol_of c (h c hc)

end GoodLemmas

section GoodEval
variable [FiniteDimensional F K]
variable (A : SampledIOSameExecutionAssignment R p)
  (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
  (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
  {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)

theorem good_gate_eq (g : CoeffExpr F) (hg : Good g) (x : F) :
    g.eval (envNew A hn nodes b chalVal pubVal orbit x) =
      g.eval (envOld A hn nodes b chalVal pubVal orbit x) := by
  refine coeff_eval_congr (E₁ := envNew A hn nodes b chalVal pubVal orbit x)
    (E₂ := envOld A hn nodes b chalVal pubVal orbit x) rfl rfl g ?_
  intro c hc
  obtain ⟨h303, hH, hR⟩ := hg c hc
  exact ⟨envNew_trace_eq_of_not_host A hn nodes b chalVal pubVal orbit c h303 hR hH x,
    envNew_traceNext_eq A hn nodes b chalVal pubVal orbit c h303 hR hH x⟩

end GoodEval

/-! ## 14. Canonical satisfaction at width 309 -/

section Satisfaction
variable [FiniteDimensional F K]

/-- **All eight source buckets of the 309 chip hold on every canonical 309 row.** -/
theorem canonical_obligations309
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hstep : ∀ (i : Fin R.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < R.problem.cfg.compRows),
      nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hchal : ExactFinalChallengeCoordinates b A chalVal)
    (hpub : ExactFinalPublicCoordinates b R hn pubVal)
    (hreq : ExactFinalRequestsCoordinate b A pubVal)
    (hln : ExactFinalLineOrigin R hn)
    (hord : 2 ≤ R.problem.cfg.compRows →
      R.problem.cfg.compRows ≤ orderOf R.computeWalkAlpha)
    (hax : FormRAxisBound A b)
    (hbasis : FormRBasis b)
    (hwidth : FormRWidth F)
    (i : Fin R.problem.cfg.compRows) :
    SourceObligations309 R.problem.cfg.compRows (Gnew A hn nodes b chalVal pubVal orbit i)
      (envNew A hn nodes b chalVal pubVal orbit (nodes i)) := by
  have hold := canonical_corrected_source_obligations A hA hn nodes hnodes b chalVal pubVal orbit
    hstep hchal hpub hreq hln hord hax hbasis hwidth i
  dsimp only at hold
  -- the last-row mask on the new decoded row
  have hb12 := base_trace_eq A hn nodes b chalVal pubVal orbit i 12
  have hcell12 := canonical_gather_base_current A hn nodes hnodes b chalVal pubVal orbit i 12
  -- the residual pins vanish off the last row
  have hres_zero : ∀ (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) (j : Fin 2),
      (residualSource309 j).eval (Gnew A hn nodes b chalVal pubVal orbit i) = 0 := by
    intro hi j
    have hsucc := hstep i hi
    have hnl : (Gold A hn nodes b chalVal pubVal orbit i).baseTrace 12 = 0 := by
      rw [hcell12]
      have : i ≠ ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩ := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      simp [finalBaseCell, this]
    have hsteps := walk_steps_eq A hn nodes hnodes b chalVal pubVal orbit i hi hsucc
    have hold_core := hold.extensionCore21 (if j = 0 then packedWalkCountId else packedWalkAccId)
    have hold_aux := hold.residualAux3 ⟨j.val, by omega⟩
    have hj2 : (⟨j.val, by omega⟩ : CorrectedResidualWitnessId) ≠ 2 := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    fin_cases j
    · change (lowerW walkCountStep309).eval (Gnew A hn nodes b chalVal pubVal orbit i) = 0
      rw [← lower309_eval _ _ _ (lower309_some _ lower309_total.1)]
      change walkCountStep309.eval (srcNew A hn nodes b chalVal pubVal orbit i) = 0
      rw [hsteps.1, srcOld_eq A hn nodes b chalVal pubVal orbit i (coreSrc ⟨74, by omega⟩)
        (finalExtTransitionGates_noWalkVars _ (List.get_mem _ _))]
      simp [correctedCoreSemanticValue, notLastScalar, hnl, packedWalkCountId, packedWalkAccId,
        packedChainId, packedLnChainId, packedWalkLnId] at hold_core
      simp [correctedAuxSemanticValue, hj2, sub_eq_zero] at hold_aux
      have := correctedFinalExtGate_eval_source (Gold A hn nodes b chalVal pubVal orbit i)
        packedWalkCountId
      rw [show coreSrc ⟨74, by omega⟩ = finalExtTransitionGates.get ⟨packedWalkCountId, by simp⟩
        from rfl, this]
      rw [show correctedFinalExtGate packedWalkCountId = correctedFinalResidualSource 0 from rfl,
        ← hold_aux]
      simpa [residualWitnessRole] using hold_core
    · change (lowerW walkAccStep309).eval (Gnew A hn nodes b chalVal pubVal orbit i) = 0
      rw [← lower309_eval _ _ _ (lower309_some _ lower309_total.2.1)]
      change walkAccStep309.eval (srcNew A hn nodes b chalVal pubVal orbit i) = 0
      rw [hsteps.2, srcOld_eq A hn nodes b chalVal pubVal orbit i (coreSrc ⟨75, by omega⟩)
        (finalExtTransitionGates_noWalkVars _ (List.get_mem _ _))]
      simp [correctedCoreSemanticValue, notLastScalar, hnl, packedWalkCountId, packedWalkAccId,
        packedChainId, packedLnChainId, packedWalkLnId] at hold_core
      simp [correctedAuxSemanticValue, hj2, sub_eq_zero] at hold_aux
      have := correctedFinalExtGate_eval_source (Gold A hn nodes b chalVal pubVal orbit i)
        packedWalkAccId
      rw [show coreSrc ⟨75, by omega⟩ = finalExtTransitionGates.get ⟨packedWalkAccId, by simp⟩
        from rfl, this]
      rw [show correctedFinalExtGate packedWalkAccId = correctedFinalResidualSource 1 from rfl,
        ← hold_aux]
      simpa [residualWitnessRole] using hold_core
  refine
    { base15 := ?_, extensionCore := ?_, residualAux := ?_, endpointDegreeTwo := ?_,
      endpointDegreeFour := ?_, selectorEquality2 := ?_, formR99 := ?_, formRLam := ?_,
      expGates := ?_ }
  · intro g hg
    rw [good_gate_eq A hn nodes b chalVal pubVal orbit g
      (good_of_lowCols (base_gates_lowCols _ g hg))]
    exact hold.base15 g hg
  · intro g
    by_cases h74 : g.val = 74
    · have hg : g = packedWalkCountId := Fin.ext h74
      subst hg
      simp only [coreSemValue309, packedWalkCountId, packedQueueNonEmptyId, packedQueueTilingId,
        correctedCoreSemanticValue]
      simp only [Fin.mk.injEq, show (74 : ℕ) ≠ 76 by omega, show (74 : ℕ) ≠ 77 by omega,
        if_false, if_true]
      by_cases hi : (i : ℕ) + 1 < R.problem.cfg.compRows
      · have hr := residual_identity A hn nodes hnodes b chalVal pubVal orbit i 0
        rw [show residualWitnessRole 0 = ⟨58 + ((0 : Fin 2) : ℕ), by omega⟩ from rfl, hr,
          hres_zero hi 0, mul_zero]
      · have hl : i = ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩ := by
          apply Fin.ext; simp; omega
        rw [notLastScalar, hb12, hcell12]
        simp [finalBaseCell, hl]
    by_cases h75 : g.val = 75
    · have hg : g = packedWalkAccId := Fin.ext h75
      subst hg
      simp only [coreSemValue309, packedWalkAccId, packedQueueNonEmptyId, packedQueueTilingId,
        correctedCoreSemanticValue, packedWalkCountId]
      simp only [Fin.mk.injEq, show (75 : ℕ) ≠ 76 by omega, show (75 : ℕ) ≠ 77 by omega,
        show (75 : ℕ) ≠ 74 by omega, if_false, if_true]
      by_cases hi : (i : ℕ) + 1 < R.problem.cfg.compRows
      · have hr := residual_identity A hn nodes hnodes b chalVal pubVal orbit i 1
        rw [show residualWitnessRole 1 = ⟨58 + ((1 : Fin 2) : ℕ), by omega⟩ from rfl, hr,
          hres_zero hi 1, mul_zero]
      · have hl : i = ⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩ := by
          apply Fin.ext; simp; omega
        rw [notLastScalar, hb12, hcell12]
        simp [finalBaseCell, hl]
    by_cases h76 : g.val = 76
    · have hg : g = packedQueueNonEmptyId := Fin.ext h76
      subst hg
      simp only [coreSemValue309, if_true]
      rw [(queue_eq A hn nodes hnodes b chalVal pubVal orbit i).1]
      have := hold.extensionCore21 packedQueueNonEmptyId
      simpa [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId, packedChainId,
        packedLnChainId, packedWalkLnId, packedQueueNonEmptyId] using this
    by_cases h77 : g.val = 77
    · have hg : g = packedQueueTilingId := Fin.ext h77
      subst hg
      simp only [coreSemValue309, packedQueueTilingId, packedQueueNonEmptyId, Fin.mk.injEq,
        show (77 : ℕ) ≠ 76 by omega, if_false, if_true]
      rw [(queue_eq A hn nodes hnodes b chalVal pubVal orbit i).2]
      have := hold.extensionCore21 packedQueueTilingId
      simpa [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId, packedChainId,
        packedLnChainId, packedWalkLnId, packedQueueTilingId] using this
    rw [coreSem_untouched A hn nodes hnodes b chalVal pubVal orbit i g h74 h75 h76 h77]
    exact hold.extensionCore21 g
  · intro j
    by_cases hj : j = 2
    · subst hj
      simp only [auxSemValue309, dif_pos rfl, correctedAuxSemanticValue, if_pos rfl]
      have hlow := correctedLowerFinal_eval (Gnew A hn nodes b chalVal pubVal orbit i).base _ _
        correctedLowerFinal_accAfterStep
      have hlow' := correctedLowerFinal_eval (Gold A hn nodes b chalVal pubVal orbit i) _ _
        correctedLowerFinal_accAfterStep
      rw [← hlow, untouched_expr_eq A hn nodes hnodes b chalVal pubVal orbit i _
        untouched_noWalk.1 (untouched_endpoint_insensitive _ _ (by simp)), hlow']
      have := hold.residualAux3 2
      simpa [correctedAuxSemanticValue] using this
    · have hidx : (aux309Idx j hj : ℕ) = j.val := rfl
      simp only [auxSemValue309, dif_neg hj, sub_eq_zero]
      have hr := residual_identity A hn nodes hnodes b chalVal pubVal orbit i (aux309Idx j hj)
      have hrole : residualWitnessRole j = ⟨58 + ((aux309Idx j hj : Fin 2) : ℕ), by omega⟩ := by
        apply Fin.ext; simp [residualWitnessRole, hidx]
      rw [hrole, hr]
  · intro t ht
    simp only [endpoint2_309, List.mem_cons, List.not_mem_nil, or_false] at ht
    have hold2 := hold.endpointDegreeTwo2
    have hmem : ∀ e, (correctedLowerFinal e).isSome →
        lowerLeaf e ∈ correctedEndpoint2.map WTyped.leaf →
        (lowerLeaf e).eval (Gnew A hn nodes b chalVal pubVal orbit i) =
          ((correctedLowerFinal e).getD (.const 0)).eval (Gold A hn nodes b chalVal pubVal orbit i) →
        (lowerLeaf e).eval (Gnew A hn nodes b chalVal pubVal orbit i) = 0 := by
      intro e _ hm heq
      rw [heq]
      obtain ⟨t', ht', hte⟩ := List.mem_map.mp hm
      simp only [lowerLeaf, WTyped.leaf.injEq] at hte
      rw [← hte]
      exact hold2 t' ht'
    have hleaf : ∀ e, (correctedLowerFinal e).isSome → noWalkVars e = true →
        Insensitive (curSel (sIdx i)) (diffAt (sIdx i)) e = true →
        (lowerLeaf e).eval (Gnew A hn nodes b chalVal pubVal orbit i) =
          ((correctedLowerFinal e).getD (.const 0)).eval (Gold A hn nodes b chalVal pubVal orbit i) := by
      intro e hs hw hins
      obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp hs
      simp only [lowerLeaf, WTyped.eval, ht', Option.getD_some]
      rw [← correctedLowerFinal_eval _ _ _ ht', ← correctedLowerFinal_eval _ _ _ ht']
      exact untouched_expr_eq A hn nodes hnodes b chalVal pubVal orbit i e hw hins
    have hins := untouched_endpoint_insensitive (sIdx i)
    have hEp := endpoints_eq A hn nodes hnodes b chalVal pubVal orbit hpub i
    have hlw : ∀ e e', (lower309 e).isSome → (correctedLowerFinal e').isSome → noWalkVars e' = true →
        lowerLeaf e' ∈ correctedEndpoint2.map WTyped.leaf →
        e.eval (srcNew A hn nodes b chalVal pubVal orbit i) =
          e'.eval (srcOld A hn nodes b chalVal pubVal orbit i) →
        (lowerW e).eval (Gnew A hn nodes b chalVal pubVal orbit i) = 0 := by
      intro e e' hs hs' hw hm heq
      rw [← lower309_eval _ _ _ (lower309_some e hs)]
      change e.eval (srcNew A hn nodes b chalVal pubVal orbit i) = 0
      rw [heq, srcOld_eq A hn nodes b chalVal pubVal orbit i e' hw]
      obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp hs'
      rw [correctedLowerFinal_eval _ _ _ ht']
      obtain ⟨t'', ht'', hte⟩ := List.mem_map.mp hm
      simp only [lowerLeaf, ht', Option.getD_some, WTyped.leaf.injEq] at hte
      rw [← hte]
      exact hold2 t'' ht''
    rw [endpoint2_309_untouched] at hmem hlw
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hmem _ lowerLeaf_total.1 (by simp) (hleaf _ lowerLeaf_total.1 untouched_noWalk.2.1
        (hins _ (by simp)))
    · exact hlw _ _ lower309_total.2.2.2.2.1 (by decide) untouched_noWalk.2.2.2.2.2.1 (by simp)
        hEp.1
    · exact hlw _ _ lower309_total.2.2.2.2.2.1 (by decide) untouched_noWalk.2.2.2.2.2.2.1
        (by simp) hEp.2.1
    · exact hmem _ lowerLeaf_total.2.1 (by simp) (hleaf _ lowerLeaf_total.2.1
        untouched_noWalk.2.2.1 (hins _ (by simp)))
    · exact hmem _ lowerLeaf_total.2.2.1 (by simp) (hleaf _ lowerLeaf_total.2.2.1
        untouched_noWalk.2.2.2.1 (hins _ (by simp)))
    · exact hmem _ lowerLeaf_total.2.2.2 (by simp) (hleaf _ lowerLeaf_total.2.2.2
        untouched_noWalk.2.2.2.2.1 (hins _ (by simp)))
  · intro t ht
    simp only [endpoint4_309, List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    have hEp := (endpoints_eq A hn nodes hnodes b chalVal pubVal orbit hpub i).2.2
    rw [← lower309_eval _ _ _ (lower309_some _ lower309_total.2.2.2.2.2.2)]
    change finalMaskedWalkAccInit309.eval (srcNew A hn nodes b chalVal pubVal orbit i) = 0
    rw [hEp, srcOld_eq A hn nodes b chalVal pubVal orbit i _ untouched_noWalk.2.2.2.2.2.2.2]
    have hs : (correctedLowerFinal OptimizedComputeFinalTypedLowering.finalMaskedWalkAccInit).isSome :=
      by decide
    obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp hs
    rw [correctedLowerFinal_eval _ _ _ ht']
    apply hold.endpointDegreeFour1
    simp [correctedEndpoint4, ht']
  · intro g hg
    rw [good_gate_eq A hn nodes b chalVal pubVal orbit g (good_of_lowCols (equality_lowCols g hg))]
    exact hold.selectorEquality2 g hg
  · intro g hg
    rw [good_gate_eq A hn nodes b chalVal pubVal orbit g (formR_good g hg)]
    exact hold.formR99 g hg
  · intro t ht
    have hc : ∀ c, lowCol c → (envNew A hn nodes b chalVal pubVal orbit (nodes i)).trace c =
        (envOld A hn nodes b chalVal pubVal orbit (nodes i)).trace c := by
      intro c hc
      exact envNew_trace_eq_of_not_host A hn nodes b chalVal pubVal orbit c
        (by unfold lowCol at hc; omega) (plainCol_of c hc).2.2 (plainCol_of c hc).2.1 _
    have hcn : ∀ c, lowCol c → (envNew A hn nodes b chalVal pubVal orbit (nodes i)).traceNext c =
        (envOld A hn nodes b chalVal pubVal orbit (nodes i)).traceNext c := by
      intro c hc
      exact envNew_traceNext_eq A hn nodes b chalVal pubVal orbit c
        (by unfold lowCol at hc; omega) (plainCol_of c hc).2.2 (plainCol_of c hc).2.1 _
    rw [typed_eval_congr_noExt (a := (Gnew A hn nodes b chalVal pubVal orbit i).base)
      (c := Gold A hn nodes b chalVal pubVal orbit i) ?_ ?_ rfl rfl rfl
      ?_ ?_ ?_ t (formRLamPins_noExt t ht)]
    · exact hold.formRLam t ht
    · funext j; exact hc j (by unfold lowCol; have := j.isLt; omega)
    · funext j; exact hcn j (by unfold lowCol; have := j.isLt; omega)
    · funext j; exact hc _ (by unfold lowCol; have := j.isLt; omega)
    · funext j
      simp only [Gnew, gather309, gatherCorrectedFinalTypedEnv]
      apply Finset.sum_congr rfl; intro k _
      rw [hc (296 + 3 * (j : ℕ) + (k : ℕ)) (by unfold lowCol; have := j.isLt; have := k.isLt; omega)]
    · exact hc 302 (by unfold lowCol; omega)
  · intro g hg
    rw [good_gate_eq A hn nodes b chalVal pubVal orbit g (good_of_lowCols (exp_lowCols g hg))]
    exact hold.expGates g hg

/-- The 309 trace binds the two preprocessing masks. -/
theorem canonical309_binds_preprocessing
    (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h) :
    (ProductionNamedComputeRAP309 hn nodes b chalVal pubVal orbit).BindsPreprocessing
      (correctedCanonicalFinalTrace309 A hn nodes b chalVal pubVal orbit) := by
  intro j
  fin_cases j
  · change correctedCanonicalFinalTrace309 A hn nodes b chalVal pubVal orbit ⟨11, by omega⟩ =
      firstRowMask nodes
    rw [trace309_eq_old A hn nodes b chalVal pubVal orbit ⟨11, by omega⟩ (by simp)
      (by simp [isHostCol]) (by simp [isResCol])]
    simp [correctedCanonicalFinalTrace, preliminaryTrace]
  · change correctedCanonicalFinalTrace309 A hn nodes b chalVal pubVal orbit ⟨12, by omega⟩ =
      lastRowMask hn nodes
    rw [trace309_eq_old A hn nodes b chalVal pubVal orbit ⟨12, by omega⟩ (by simp)
      (by simp [isHostCol]) (by simp [isResCol])]
    simp [correctedCanonicalFinalTrace, preliminaryTrace]

/-- **`canonical_satisfies309`**: the honest 309 trace satisfies the un-hosted chip, under exactly
the hypotheses of the deployed `correctedCanonicalFinalTrace_satisfies`. -/
theorem canonical_satisfies309
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hstep : ∀ (i : Fin R.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < R.problem.cfg.compRows),
      nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hchal : ExactFinalChallengeCoordinates b A chalVal)
    (hpub : ExactFinalPublicCoordinates b R hn pubVal)
    (hreq : ExactFinalRequestsCoordinate b A pubVal)
    (hln : ExactFinalLineOrigin R hn)
    (hord : 2 ≤ R.problem.cfg.compRows →
      R.problem.cfg.compRows ≤ orderOf R.computeWalkAlpha)
    (hax : FormRAxisBound A b)
    (hbasis : FormRBasis b)
    (hwidth : FormRWidth F) :
    RAP.SatisfiesWithPreprocessing
      (ProductionNamedComputeRAP309 hn nodes b chalVal pubVal orbit)
      (correctedCanonicalFinalTrace309 A hn nodes b chalVal pubVal orbit) := by
  erw [satisfies309_iff_sourceLanguage]
  refine ⟨canonical309_binds_preprocessing A hn nodes b chalVal pubVal orbit, ?_⟩
  intro x hx
  obtain ⟨i, _, hix⟩ :=
    (@Finset.mem_image _ _ (fun a b => Classical.propDecidable (a = b)) nodes Finset.univ x).mp hx
  subst x
  exact canonical_obligations309 A hA hn nodes hnodes b chalVal pubVal orbit hstep hchal hpub hreq
    hln hord hax hbasis hwidth i

end Satisfaction


#print axioms canonical_satisfies309
#print axioms canonical_obligations309

end
end Unhosted309
end Nock.NockVMROM.Thm54
