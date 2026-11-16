/-
  Nock/NockVMROM/Thm54/P8Core/PartAReHost.lean

  Below the statement.

  The deployed compute chip (303) hosts the walk `count` / `acc` in the two host `𝕂`-roles of each
  row's own state (`3·overlayANat st`, `+1`); the un-hosted chip (309, L2) reads them from the walk
  columns `W0 = 303..305`, `W1 = 306..308`.  `reHost P c Qc : Fin 303 → F[X]`:

  * on a row of state `s` (decoded from the 309 selectors), the host cells of `s` take the walk
    values `W0`, `W1` of that row; every other cell is `Qc`'s (`preHost309`);
  * the residual roles `58`/`59` interpolate the deployed (hosted) walk recurrences on that trace
    (`reHost309`);
  * every other column is `Qc`'s, verbatim.

`satisfies303_of_309`: acceptance of `Qc` by the 309 chip at a tuple gives acceptance of
  `reHost P c Qc` by the deployed 303 chip at the same tuple.

  Scope: `repartitionedChronology` and the parallel package.  -- the paper
-/
import Nock.NockVMROM.Thm54.Unhosted309Canonical
import Nock.NockVMROM.Thm54.P8Core.PartAStaged12
import Nock.NockVMROM.Thm54.P8Core.DeployedComputeRows

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 300000

namespace Nock.NockVMROM.Thm54.PartAReHost

open scoped Polynomial
open Polynomial
open Nock Nock.Reified Nock.ComputeTable
open Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinal hiding residualWitnessRole ResidualWitnessId FinalExtensionColumn
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Module

noncomputable section

/-! ## 1. One-hot selectors from the shared base gates -/

section OneHot
variable {F : Type} [Field F]

/-- The base gates (shared by the 303 and the 309 chips) force one-hot selectors. -/
theorem selectors_oneHot (n : ℕ) (E : Env F)
    (hb : ∀ g ∈ finalBaseTransitionGates (F := F) n, g.eval E = 0)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : F) = 1 → m = 1) :
    ∃ s : Fin 11, ∀ j, j < 11 → E.trace j = if j = (s : ℕ) then 1 else 0 := by
  have hbool : ∀ k, k < 11 → E.trace k = 0 ∨ E.trace k = 1 := by
    intro k hk
    have hg := hb (selectorBool k) (by
      simp only [finalBaseTransitionGates, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl ⟨k, hk, rfl⟩)
    simp only [selectorBool, bv, CoeffExpr.eval, mul_eq_zero, sub_eq_zero] at hg
    rcases hg with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  have hsum : E.trace 0 + E.trace 1 + E.trace 2 + E.trace 3 + E.trace 4 + E.trace 5 +
      E.trace 6 + E.trace 7 + E.trace 8 + E.trace 9 + E.trace 10 = 1 := by
    have hg := hb selectorOneHot (by simp [finalBaseTransitionGates])
    simp [selectorOneHot, selectorSum, CoeffExpr.sumList, List.range_succ, bv, CoeffExpr.eval,
      sub_eq_zero] at hg
    linear_combination hg
  obtain ⟨st, hst⟩ := Nock.ComputeTable.oneHot_of_bool_sum
    (fun st => E.trace (Nock.Reified.opCol st)) hchar
    (fun st => hbool _ (by cases st <;> decide))
    (by simp only [Nock.ComputeTable.sum09, Nock.Reified.opCol]; linear_combination hsum)
  refine ⟨OptimizedComputeCodec.stateIndex st, fun j hj => ?_⟩
  have hidx : ((OptimizedComputeCodec.stateIndex st : Fin 11) : ℕ) = Nock.Reified.opCol st := by
    cases st <;> rfl
  rw [hidx]
  have key : ∀ s' : State, E.trace (Nock.Reified.opCol s') =
      if Nock.Reified.opCol s' = Nock.Reified.opCol st then 1 else 0 := by
    intro s'
    have := congrFun hst s'
    simp only [Nock.ComputeTable.opSel] at this
    rw [this]
    by_cases h : s' = st
    · subst h; simp
    · have : Nock.Reified.opCol s' ≠ Nock.Reified.opCol st := by
        intro he; apply h
        cases s' <;> cases st <;> simp_all [Nock.Reified.opCol]
      simp [h, this]
  have hj' : ∃ s' : State, Nock.Reified.opCol s' = j := by
    interval_cases j
    · exact ⟨.s0, rfl⟩
    · exact ⟨.s1, rfl⟩
    · exact ⟨.s2, rfl⟩
    · exact ⟨.s3, rfl⟩
    · exact ⟨.s4, rfl⟩
    · exact ⟨.s5, rfl⟩
    · exact ⟨.s6, rfl⟩
    · exact ⟨.s7, rfl⟩
    · exact ⟨.s8, rfl⟩
    · exact ⟨.s9, rfl⟩
    · exact ⟨.cons, rfl⟩
  obtain ⟨s', rfl⟩ := hj'
  rw [key s']

end OneHot


/-! ## 2. The re-hosted trace -/

section Defs

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The compute row count. -/
abbrev nC : ℕ := P.optimized.family.problem.cfg.compRows

/-- The selector value `j < 11` of a 309 trace at row `i`. -/
def selAt (Qc : Fin 309 → F[X]) (i : Fin (nC P)) (j : ℕ) : F :=
  if h : j < 309 then (Qc ⟨j, h⟩).eval (P.optimized.computeNodes i) else 0

open Classical in
/-- **The state index of row `i`**, decoded from the 309 selectors (the one-hot index when they are
one-hot, which acceptance forces; `0` otherwise). -/
def rowIdx (Qc : Fin 309 → F[X]) (i : Fin (nC P)) : Fin 11 :=
  if h : ∃ s : Fin 11, ∀ j, j < 11 → selAt P Qc i j = if j = (s : ℕ) then 1 else 0 then
    Classical.choose h
  else 0

/-- The row state. -/
abbrev rowSt (Qc : Fin 309 → F[X]) (i : Fin (nC P)) : State := stOfIdx (rowIdx P Qc i)

/-- **The re-hosted cell** of physical column `j` at row `i`: on the two host roles of the row's
state, the walk column limbs (`W0`, `W1`); elsewhere the 309 cell. -/
def hostCell (Qc : Fin 309 → F[X]) (i : Fin (nC P)) (j : ℕ) : F :=
  if (j - 13) / 3 = 3 * overlayANat (rowSt P Qc i) then
    selAt P Qc i (303 + (j - 13) % 3)
  else if (j - 13) / 3 = 3 * overlayANat (rowSt P Qc i) + 1 then
    selAt P Qc i (306 + (j - 13) % 3)
  else selAt P Qc i j

/-- **Stage one**: the host columns re-hosted, every other column the 309 trace's. -/
def preHost309 (Qc : Fin 309 → F[X]) : Fin 309 → F[X] := fun j =>
  if isHostCol j then interp P.optimized.computeNodes fun i => hostCell P Qc i j else Qc j

/-- The deployed compute row environment of a 309 trace at tuple `t`, row `i`. -/
abbrev envAt (t : OptimizedProductionChallengeTuple K F) (Q : Fin 309 → F[X]) (i : Fin (nC P)) :
    Env F :=
  envOfTrace Q P.optimized.orbit.ω (P.optimized.computeNodes i)
    (computeChalValOfTuple P.optimized.basis t) (P.familyComputePublic t)

/-- The residual index of a residual column. -/
def resIdx (j : ℕ) : CorrectedResidualWitnessId :=
  if (j - 13) / 3 = 59 then 1 else 0

/-- **The re-hosted 309 trace**: stage one, with the residual roles `58`/`59` interpolating the
deployed (hosted) walk recurrences of stage one. -/
def reHost309 (t : OptimizedProductionChallengeTuple K F) (Qc : Fin 309 → F[X]) :
    Fin 309 → F[X] := fun j =>
  if isResCol j then
    interp P.optimized.computeNodes fun i =>
      coord P.optimized.basis
        ((correctedFinalResidualSource (resIdx j)).eval
          (gatherCorrectedFinalTypedEnv P.optimized.basis (envAt P t (preHost309 P Qc) i)))
        ⟨(j - 13) % 3, Nat.mod_lt _ (by omega)⟩
  else preHost309 P Qc j

/-- **`reHost`** — the re-hosted trace at the deployed width `303`. -/
def reHost (t : OptimizedProductionChallengeTuple K F) (Qc : Fin 309 → F[X]) :
    Fin P.computeChip.rap.w → F[X] := fun j =>
  reHost309 P t Qc ⟨j, by have := j.isLt; have h := PartAStaged.computeWidth303 P; omega⟩

end Defs


/-! ## 3. Cells of the re-hosted trace -/

section Cells

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (t : OptimizedProductionChallengeTuple K F) (Qc : Fin 309 → F[X])

/-- One-hot selectors on every row (forced by acceptance, `oneHot_of_sat`). -/
def OneHotRows : Prop :=
  ∀ i : Fin (nC P), ∀ j, j < 11 → selAt P Qc i j = if j = (rowIdx P Qc i : ℕ) then 1 else 0

theorem rowIdx_spec (i : Fin (nC P))
    (h : ∃ s : Fin 11, ∀ j, j < 11 → selAt P Qc i j = if j = (s : ℕ) then 1 else 0) :
    ∀ j, j < 11 → selAt P Qc i j = if j = (rowIdx P Qc i : ℕ) then 1 else 0 := by
  classical
  unfold rowIdx
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem hostRoles_isHost (st : State) (w : Fin 2) (k : Fin 3) :
    isHostCol (13 + 3 * (3 * overlayANat st + (w : ℕ)) + (k : ℕ)) = true ∧
      isResCol (13 + 3 * (3 * overlayANat st + (w : ℕ)) + (k : ℕ)) = false := by
  have hw := w.isLt; have hk := k.isLt
  cases st <;> simp [isHostCol, isResCol, hostKRoles, overlayANat, decide_eq_false_iff_not] <;> refine ⟨?_, decide_eq_false ?_⟩ <;> omega

theorem hostCell_off (i : Fin (nC P)) (j : ℕ)
    (h : (j - 13) / 3 ∉ hostRolesOf (rowSt P Qc i)) : hostCell P Qc i j = selAt P Qc i j := by
  simp only [hostRolesOf, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  unfold hostCell
  rw [if_neg h.1, if_neg h.2]

theorem selAt_eval (i : Fin (nC P)) (j : Fin 309) :
    selAt P Qc i j = (Qc j).eval (P.optimized.computeNodes i) := by
  unfold selAt; rw [dif_pos j.isLt]

/-- **Current row**: the re-hosted and the 309 rows agree off the residual columns and the host
roles of the row's state. -/
theorem e303_trace (i : Fin (nC P)) (c : ℕ) (hc : c < 309) (hR : isResCol c = false)
    (hH : isHostCol c = true → (c - 13) / 3 ∉ hostRolesOf (rowSt P Qc i)) :
    (envAt P t (reHost309 P t Qc) i).trace c = (envAt P t Qc i).trace c := by
  simp only [envAt, envOfTrace, dif_pos hc]
  simp only [reHost309, hR, Bool.false_eq_true, if_false, preHost309]
  by_cases hh : isHostCol c = true
  · rw [if_pos hh, interp_eval _ P.optimized.computeNodes_injective,
      hostCell_off P Qc i c (hH hh), selAt]
    rw [dif_pos hc]
  · rw [if_neg hh]

/-- **Successor row**: they agree off the residual and all host columns. -/
theorem e303_traceNext (i : Fin (nC P)) (c : ℕ) (hc : c < 309) (hR : isResCol c = false)
    (hH : isHostCol c = false) :
    (envAt P t (reHost309 P t Qc) i).traceNext c = (envAt P t Qc i).traceNext c := by
  simp only [envAt, envOfTrace, dif_pos hc]
  simp only [reHost309, hR, Bool.false_eq_true, if_false, preHost309, hH]

theorem e303_trace_plain (i : Fin (nC P)) (c : ℕ) (hc : c < 309) (hR : isResCol c = false)
    (hH : isHostCol c = false) :
    (envAt P t (reHost309 P t Qc) i).trace c = (envAt P t Qc i).trace c :=
  e303_trace P t Qc i c hc hR (fun h => by simp [hH] at h)

/-- **The host cells of the row's state carry the walk columns.** -/
theorem e303_host (i : Fin (nC P)) (w : Fin 2) (k : Fin 3) :
    (envAt P t (reHost309 P t Qc) i).trace
        (13 + 3 * (3 * overlayANat (rowSt P Qc i) + (w : ℕ)) + (k : ℕ)) =
      (envAt P t Qc i).trace (303 + 3 * (w : ℕ) + (k : ℕ)) := by
  have hhost := hostRoles_isHost (rowSt P Qc i) w k
  have hw := w.isLt; have hk := k.isLt
  have hlt : 13 + 3 * (3 * overlayANat (rowSt P Qc i) + (w : ℕ)) + (k : ℕ) < 309 := by
    have : overlayANat (rowSt P Qc i) ≤ 9 := by cases rowSt P Qc i <;> decide
    omega
  simp only [envAt, envOfTrace, dif_pos hlt, dif_pos (show 303 + 3 * (w : ℕ) + (k : ℕ) < 309 by omega)]
  simp only [reHost309, hhost.2, Bool.false_eq_true, if_false, preHost309, hhost.1, if_true]
  rw [interp_eval _ P.optimized.computeNodes_injective]
  unfold hostCell
  have e1 : (13 + 3 * (3 * overlayANat (rowSt P Qc i) + (w : ℕ)) + (k : ℕ) - 13) / 3 =
      3 * overlayANat (rowSt P Qc i) + (w : ℕ) := by omega
  have e2 : (13 + 3 * (3 * overlayANat (rowSt P Qc i) + (w : ℕ)) + (k : ℕ) - 13) % 3 = k := by
    omega
  rw [e1, e2]
  fin_cases w
  · simp [selAt, show (303 : ℕ) + (k : ℕ) < 309 by omega]
  · simp [selAt, show (306 : ℕ) + (k : ℕ) < 309 by omega]

/-- The final and stage-one rows agree off the residual columns. -/
theorem e303_eq_pre (i : Fin (nC P)) (c : ℕ) (hR : isResCol c = false) :
    (envAt P t (reHost309 P t Qc) i).trace c = (envAt P t (preHost309 P Qc) i).trace c ∧
      (envAt P t (reHost309 P t Qc) i).traceNext c =
        (envAt P t (preHost309 P Qc) i).traceNext c := by
  simp only [envAt, envOfTrace]
  by_cases hc : c < 309
  · simp only [dif_pos hc, reHost309, hR, Bool.false_eq_true, if_false]
    exact ⟨trivial, trivial⟩
  · simp only [dif_neg hc]
    exact ⟨trivial, trivial⟩

/-- **The residual cells carry the hosted walk recurrences of stage one.** -/
theorem e303_res (i : Fin (nC P)) (j : Fin 2) (k : Fin 3) :
    (envAt P t (reHost309 P t Qc) i).trace (13 + 3 * (58 + (j : ℕ)) + (k : ℕ)) =
      coord P.optimized.basis
        ((correctedFinalResidualSource ⟨j, by omega⟩).eval
          (gatherCorrectedFinalTypedEnv P.optimized.basis (envAt P t (preHost309 P Qc) i))) k := by
  have hj := j.isLt; have hk := k.isLt
  have hres : isResCol (13 + 3 * (58 + (j : ℕ)) + (k : ℕ)) = true := by
    simp [isResCol]; omega
  simp only [envAt, envOfTrace, dif_pos (show 13 + 3 * (58 + (j : ℕ)) + (k : ℕ) < 309 by omega),
    reHost309, hres, if_true]
  rw [interp_eval _ P.optimized.computeNodes_injective]
  have e1 : resIdx (13 + 3 * (58 + (j : ℕ)) + (k : ℕ)) = ⟨j, by omega⟩ := by
    unfold resIdx
    fin_cases j
    · simp; omega
    · simp; omega
  have e2 : (⟨(13 + 3 * (58 + (j : ℕ)) + (k : ℕ) - 13) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = k :=
    Fin.ext (by simp; omega)
  rw [e1, e2]

end Cells


/-! ## 4. Source-level agreement and the selectors -/

section Source

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (t : OptimizedProductionChallengeTuple K F) (Qc : Fin 309 → F[X])

/-- The decoded 309 row. -/
abbrev S309 (i : Fin (nC P)) : Env K := (gather309 P.optimized.basis (envAt P t Qc i)).toSourceEnv
/-- The decoded re-hosted row (read through the same decoder; the walk columns are `Qc`'s). -/
abbrev S303 (i : Fin (nC P)) : Env K :=
  (gather309 P.optimized.basis (envAt P t (reHost309 P t Qc) i)).toSourceEnv

theorem sel309 (hone : OneHotRows P Qc) (i : Fin (nC P)) (j : ℕ) (hj : j < 11) :
    (envAt P t Qc i).trace j = if j = (rowIdx P Qc i : ℕ) then 1 else 0 := by
  have h := hone i j hj
  simp only [selAt, dif_pos (show j < 309 by omega)] at h
  simp only [envAt, envOfTrace, dif_pos (show j < 309 by omega)]
  exact h

theorem sel303 (hone : OneHotRows P Qc) (i : Fin (nC P)) (j : ℕ) (hj : j < 11) :
    (envAt P t (reHost309 P t Qc) i).trace j = if j = (rowIdx P Qc i : ℕ) then 1 else 0 := by
  rw [e303_trace_plain P t Qc i j (by omega) (by simp [isResCol]; omega)
    (by simp [isHostCol]; omega)]
  exact sel309 P t Qc hone i j hj

theorem matches309 (hone : OneHotRows P Qc) (i : Fin (nC P)) :
    Matches (curSel (rowIdx P Qc i)) (S309 P t Qc i) :=
  matches_curSel_of P.optimized.basis (sel309 P t Qc hone i)

theorem matches303 (hone : OneHotRows P Qc) (i : Fin (nC P)) :
    Matches (curSel (rowIdx P Qc i)) (S303 P t Qc i) :=
  matches_curSel_of P.optimized.basis (sel303 P t Qc hone i)

/-- **The decoded rows agree off `diffAt` of the row's state.** -/
theorem src_agreeH (i : Fin (nC P)) :
    ∀ k j, diffAt (rowIdx P Qc i) k j = false →
      varVal (S303 P t Qc i) k j = varVal (S309 P t Qc i) k j := by
  intro k j hd
  cases k
  · simp only [diffAt, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hd
    apply src_trace_congr
    intro c hc
    unfold physOf at hc
    apply e303_trace P t Qc i c (by omega)
    · simp only [isResCol, decide_eq_false_iff_not]
      simp only [residualRoles, List.mem_cons, List.not_mem_nil, or_false] at hd
      omega
    · intro hh
      simp only [isHostCol, decide_eq_true_eq] at hh
      simp only [rowSt, hostRolesOf, residualRoles, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
      omega
  · simp only [diffAt, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hd
    apply src_traceNext_congr
    intro c hc
    unfold physOf at hc
    apply e303_traceNext P t Qc i c (by omega)
    · simp only [isResCol, decide_eq_false_iff_not]
      simp only [residualRoles, hostKRoles, List.mem_cons, List.not_mem_nil, or_false] at hd
      omega
    · simp only [isHostCol, decide_eq_false_iff_not]
      simp only [residualRoles, hostKRoles, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
      omega
  · exact src_chal_eq P.optimized.basis rfl j
  · exact src_pub_eq P.optimized.basis rfl j

theorem succ_node (i : Fin (nC P)) (hi : (i : ℕ) + 1 < nC P) :
    P.optimized.computeNodes ⟨(i : ℕ) + 1, hi⟩ = P.optimized.orbit.ω * P.optimized.computeNodes i :=
  P.optimized.computeAdjacentOrbit i hi

/-- **Successor-row agreement** at a nonterminal row, off `diffNext` of the successor's state. -/
theorem src_agree_nextH (i : Fin (nC P)) (hi : (i : ℕ) + 1 < nC P) :
    ∀ k j, diffNext (rowIdx P Qc ⟨(i : ℕ) + 1, hi⟩) k j = false →
      varVal (S303 P t Qc i) k j = varVal (S309 P t Qc i) k j := by
  intro k j hd
  cases k
  · simp only [diffNext, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hd
    apply src_trace_congr
    intro c hc
    unfold physOf at hc
    apply e303_trace_plain P t Qc i c (by omega)
    · simp only [isResCol, decide_eq_false_iff_not]
      simp only [residualRoles, hostKRoles, List.mem_cons, List.not_mem_nil, or_false] at hd
      omega
    · simp only [isHostCol, decide_eq_false_iff_not]
      simp only [residualRoles, hostKRoles, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
      omega
  · simp only [diffNext, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hd
    apply src_traceNext_congr
    intro c hc
    unfold physOf at hc
    have h := e303_trace P t Qc ⟨(i : ℕ) + 1, hi⟩ c (by omega)
      (by simp only [isResCol, decide_eq_false_iff_not]
          simp only [residualRoles, List.mem_cons, List.not_mem_nil, or_false] at hd
          omega)
      (by intro hh
          simp only [isHostCol, decide_eq_true_eq] at hh
          simp only [rowSt, hostRolesOf, residualRoles, List.mem_cons, List.not_mem_nil,
            or_false] at hd ⊢
          omega)
    simp only [envAt, envOfTrace] at h ⊢
    rw [← succ_node P i hi]
    exact h
  · exact src_chal_eq P.optimized.basis rfl j
  · exact src_pub_eq P.optimized.basis rfl j

theorem matches_nextH (i : Fin (nC P)) (hi : (i : ℕ) + 1 < nC P)
    (Q : Fin 309 → F[X])
    (hs : ∀ j, j < 11 → (envAt P t Q ⟨(i : ℕ) + 1, hi⟩).trace j =
      if j = (rowIdx P Qc ⟨(i : ℕ) + 1, hi⟩ : ℕ) then 1 else 0) :
    Matches (nextSel (rowIdx P Qc ⟨(i : ℕ) + 1, hi⟩))
      (gather309 P.optimized.basis (envAt P t Q i)).toSourceEnv := by
  intro k j v hσ
  cases k <;> simp only [nextSel, reduceCtorEq] at hσ
  by_cases hj : j < 11
  · simp only [hj, if_true, Option.some.injEq] at hσ
    subst hσ
    have h13 : j < 13 := by omega
    have hsj := hs j hj
    simp only [varVal, Env309.toSourceEnv, gather309, CorrectedFinalTypedEnv.toSourceEnv,
      gatherCorrectedFinalTypedEnv, show j ≠ 303 by omega, show j ≠ 306 by omega, if_false,
      dif_pos h13]
    simp only [envAt, envOfTrace] at hsj ⊢
    rw [← succ_node P i hi, hsj]
    split_ifs <;> simp
  · simp [hj] at hσ

theorem matches_next309 (hone : OneHotRows P Qc) (i : Fin (nC P)) (hi : (i : ℕ) + 1 < nC P) :
    Matches (nextSel (rowIdx P Qc ⟨(i : ℕ) + 1, hi⟩)) (S309 P t Qc i) :=
  matches_nextH P t Qc i hi Qc (sel309 P t Qc hone _)

theorem matches_next303 (hone : OneHotRows P Qc) (i : Fin (nC P)) (hi : (i : ℕ) + 1 < nC P) :
    Matches (nextSel (rowIdx P Qc ⟨(i : ℕ) + 1, hi⟩)) (S303 P t Qc i) :=
  matches_nextH P t Qc i hi _ (sel303 P t Qc hone _)

end Source


/-! ## 5. The hosted reads under the one-hot selectors (specialisation normal forms) -/

/-- Terminal-row valuation: the current selectors and the public terminal-state masks
(publics `31..41`), both one-hot at `s`. -/
def lastSel (s : Fin 11) : Valuation
  | .traceCur, j => if j < 11 then some (if j = (s : ℕ) then 1 else 0) else none
  | .publicVal, j => if 31 ≤ j ∧ j < 42 then some (if j = 31 + (s : ℕ) then 1 else 0) else none
  | _, _ => none

/-- **Decided**: under the current one-hot selectors the hosted overlay read is the host role of
the row's state. -/
theorem overlay_nf_cur : ∀ s : Fin 11, ∀ c : Fin 2,
    simp0 (specSel (curSel s) (overlayCoord .traceCur c)) =
      .Mul (.Const 1) (.Var .traceCur (13 + 3 * overlayANat (stOfIdx s) + c)) := by decide

theorem overlay_nf_next : ∀ s : Fin 11, ∀ c : Fin 2,
    simp0 (specSel (nextSel s) (overlayCoord .traceNext c)) =
      .Mul (.Const 1) (.Var .traceNext (13 + 3 * overlayANat (stOfIdx s) + c)) := by decide

theorem initial_nf : ∀ s : Fin 11, ∀ c : Fin 2,
    simp0 (specSel (firstSel s) (initialOverlayCoord c)) =
      .Mul (.Const 1) (.Var .traceCur (13 + 3 * overlayANat (stOfIdx s) + c)) := by decide

theorem terminal_nf : ∀ s : Fin 11, ∀ c : Fin 2,
    simp0 (specSel (lastSel s) (terminalOverlayCoord c)) =
      .Mul (.Const 1) (.Var .traceCur (13 + 3 * overlayANat (stOfIdx s) + c)) := by decide

section Hosted

variable {K : Type} [Field K]

theorem eval_of_nf {σ : Valuation} {e : Expr} {k : VarKind} {j : ℕ}
    (hnf : simp0 (specSel σ e) = .Mul (.Const 1) (.Var k j)) {E : Env K} (hm : Matches σ E) :
    e.eval E = varVal E k j := by
  rw [← specSel_eval σ E hm, ← simp0_eval E, hnf]
  cases k <;> simp [Expr.eval, varVal]

end Hosted

section HostedPkg

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (t : OptimizedProductionChallengeTuple K F) (Qc : Fin 309 → F[X])

/-- The re-hosted host role of the row's state reads the 309 walk column. -/
theorem host_role_S303 (i : Fin (nC P)) (c : Fin 2) :
    (S303 P t Qc i).trace (13 + 3 * overlayANat (rowSt P Qc i) + (c : ℕ)) =
      (S309 P t Qc i).trace (303 + 3 * (c : ℕ)) := by
  have hc := c.isLt
  have hov : overlayANat (rowSt P Qc i) ≤ 9 := by cases rowSt P Qc i <;> decide
  have h1 : ¬ (13 + 3 * overlayANat (rowSt P Qc i) + (c : ℕ) < 13) := by omega
  have h2 : 13 + 3 * overlayANat (rowSt P Qc i) + (c : ℕ) < 76 := by omega
  have hne3 : 13 + 3 * overlayANat (rowSt P Qc i) + (c : ℕ) ≠ 303 := by omega
  have hne6 : 13 + 3 * overlayANat (rowSt P Qc i) + (c : ℕ) ≠ 306 := by omega
  simp only [Env309.toSourceEnv, gather309, CorrectedFinalTypedEnv.toSourceEnv,
    gatherCorrectedFinalTypedEnv, hne3, hne6, if_false, dif_neg h1, dif_pos h2,
    correctedFinalExtCoordIndex]
  fin_cases c
  · simp only [Fin.val_zero, add_zero, show (303 : ℕ) + 3 * 0 = 303 by rfl, if_true]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := e303_host P t Qc i 0 k
    simp only [Fin.val_zero, add_zero] at h
    rw [show 13 + 3 * (13 + 3 * overlayANat (rowSt P Qc i) - 13) + (k : ℕ) =
      13 + 3 * (3 * overlayANat (rowSt P Qc i)) + (k : ℕ) by omega, h]
    rfl
  · simp only [Fin.val_one, show (303 : ℕ) + 3 * 1 = 306 by rfl, if_true,
      show (306 : ℕ) ≠ 303 by omega, if_false]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := e303_host P t Qc i 1 k
    simp only [Fin.val_one] at h
    rw [show 13 + 3 * (13 + 3 * overlayANat (rowSt P Qc i) + 1 - 13) + (k : ℕ) =
      13 + 3 * (3 * overlayANat (rowSt P Qc i) + 1) + (k : ℕ) by omega, h]
    rfl

end HostedPkg


/-! ## 6. The retargeted sources against the hosted ones -/

section Walk

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (t : OptimizedProductionChallengeTuple K F) (Qc : Fin 309 → F[X])
  (hone : OneHotRows P Qc)

include hone in
/-- The hosted current overlay of the re-hosted row is the 309 walk column. -/
theorem overlay_cur_eq (i : Fin (nC P)) (c : Fin 2) :
    (overlayCoord .traceCur c).eval (S303 P t Qc i) = (S309 P t Qc i).trace (303 + 3 * (c : ℕ)) := by
  rw [eval_of_nf (overlay_nf_cur (rowIdx P Qc i) c) (matches303 P t Qc hone i)]
  exact host_role_S303 P t Qc i c

include hone in
/-- The hosted successor overlay at a nonterminal row is the 309 successor walk column. -/
theorem overlay_next_eq (i : Fin (nC P)) (hi : (i : ℕ) + 1 < nC P) (c : Fin 2) :
    (overlayCoord .traceNext c).eval (S303 P t Qc i) =
      (S309 P t Qc i).traceNext (303 + 3 * (c : ℕ)) := by
  rw [eval_of_nf (overlay_nf_next (rowIdx P Qc ⟨(i : ℕ) + 1, hi⟩) c)
    (matches_next303 P t Qc hone i hi)]
  have h := host_role_S303 P t Qc ⟨(i : ℕ) + 1, hi⟩ c
  simp only [varVal]
  have e1 : (S303 P t Qc i).traceNext (13 + 3 * overlayANat (stOfIdx (rowIdx P Qc ⟨(i : ℕ) + 1, hi⟩)) + (c : ℕ)) =
      (S303 P t Qc ⟨(i : ℕ) + 1, hi⟩).trace (13 + 3 * overlayANat (rowSt P Qc ⟨(i : ℕ) + 1, hi⟩) + (c : ℕ)) := by
    simp only [S303, envAt, Env309.toSourceEnv, gather309, CorrectedFinalTypedEnv.toSourceEnv,
      gatherCorrectedFinalTypedEnv, envOfTrace, succ_node P i hi]
  have e2 : (S309 P t Qc i).traceNext (303 + 3 * (c : ℕ)) =
      (S309 P t Qc ⟨(i : ℕ) + 1, hi⟩).trace (303 + 3 * (c : ℕ)) := by
    simp only [S309, envAt, Env309.toSourceEnv, gather309, CorrectedFinalTypedEnv.toSourceEnv,
      gatherCorrectedFinalTypedEnv, envOfTrace, succ_node P i hi]
  rw [e1, e2, h]

/-- The residual sources read no residual role (decided). -/
def resOK303 : VarKind × ℕ → Bool
  | (.traceCur, j) | (.traceNext, j) => decide (j ≠ 71 ∧ j ≠ 72)
  | _ => true

theorem hosted_residual_reads_ok :
    (∀ q ∈ readsE (coreSrc ⟨74, by omega⟩), resOK303 q = true) ∧
      (∀ q ∈ readsE (coreSrc ⟨75, by omega⟩), resOK303 q = true) := by decide

include hone in
/-- **The walk recurrences at 309 are the hosted ones on the re-hosted row** (nonterminal row). -/
theorem walk_steps_eqH (i : Fin (nC P)) (hi : (i : ℕ) + 1 < nC P) :
    walkCountStep309.eval (S309 P t Qc i) = (coreSrc ⟨74, by omega⟩).eval (S303 P t Qc i) ∧
      walkAccStep309.eval (S309 P t Qc i) = (coreSrc ⟨75, by omega⟩).eval (S303 P t Qc i) := by
  set s' := rowIdx P Qc ⟨(i : ℕ) + 1, hi⟩
  have hag := src_agree_nextH P t Qc i hi
  have hmn := matches_next303 P t Qc hone i hi
  have hmo := matches_next309 P t Qc hone i hi
  have hrec := next_labels_insensitive s'
  have hcm := eval_eq_of_insensitive _ _ _ hrec.2.2 matches_noSel matches_noSel hag
  have hlab := eval_eq_of_insensitive _ _ _ hrec.1 hmn hmo hag
  have hcc := eval_eq_of_insensitive _ _ _ hrec.2.1 hmn hmo hag
  have hln : (S303 P t Qc i).traceNext 74 = (S309 P t Qc i).traceNext 74 :=
    hag .traceNext 74 (diffNext_line s')
  have hc0 := overlay_cur_eq P t Qc hone i 0
  have hc1 := overlay_cur_eq P t Qc hone i 1
  have hn0 := overlay_next_eq P t Qc hone i hi 0
  have hn1 := overlay_next_eq P t Qc hone i hi 1
  norm_num at hc0 hc1 hn0 hn1
  constructor
  · rw [coreSrc74]
    simp only [walkCountStep309, Expr.eval_subst, Trans.walkCountStep, Expr.eval, Env.ofSubst,
      Trans.tn, tc, finalWalkSubstInGate309, ComputeWalkLabel.finalWalkSubstInGate, walkCountCol]
    rw [hc0, hn0, hcm]
  · rw [coreSrc75]
    simp only [walkAccStep309, Expr.eval_subst, Trans.walkAccStep, Expr.eval, Env.ofSubst,
      Trans.tn, tc, finalWalkSubstInGate309, ComputeWalkLabel.finalWalkSubstInGate, walkCountCol,
      walkAccCol, finalWalkLine, finalWalkLineIndex, finalWalkLineRole, ext0]
    rw [hc0, hc1, hn1, hlab, hcc, hln]

end Walk


/-! ## 7. Masks, endpoint publics, the first and last rows -/

section Endpoints

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (t : OptimizedProductionChallengeTuple K F) (Qc : Fin 309 → F[X])

/-- The first row. -/
abbrev row0 : Fin (nC P) := ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩
/-- The last row. -/
abbrev rowL : Fin (nC P) :=
  ⟨nC P - 1, Nat.sub_lt P.optimized.family.problem.cfg.compRows_pos (by omega)⟩

/-- **The row hypotheses** the transfer needs, all forced by acceptance at the 309 chip
(`rowHyps_of_sat`): one-hot selectors, the endpoint masks, and the endpoint publics equal to the
first / last rows' selectors (the 22 equality checks). -/
structure RowHyps : Prop where
  hone : OneHotRows P Qc
  mask11 : ∀ i, (envAt P t Qc i).trace 11 = if (i : ℕ) = 0 then 1 else 0
  mask12 : ∀ i, (envAt P t Qc i).trace 12 = if i = rowL P then 1 else 0
  pubF : ∀ j, j < 11 → P.familyComputePublic t (20 + j) =
    if j = (rowIdx P Qc (row0 P) : ℕ) then 1 else 0
  pubL : ∀ j, j < 11 → P.familyComputePublic t (31 + j) =
    if j = (rowIdx P Qc (rowL P) : ℕ) then 1 else 0

variable {P t Qc}

theorem matches_first_of (h : RowHyps P t Qc) (Q : Fin 309 → F[X])
    (hs : ∀ j, j < 11 → (envAt P t Q (row0 P)).trace j =
      if j = (rowIdx P Qc (row0 P) : ℕ) then 1 else 0) :
    Matches (firstSel (rowIdx P Qc (row0 P)))
      (gather309 P.optimized.basis (envAt P t Q (row0 P))).toSourceEnv := by
  have hcur := matches_curSel_of P.optimized.basis hs
  intro k j v hσ
  cases k
  · exact hcur .traceCur j v (by simpa [firstSel, curSel] using hσ)
  · simp [firstSel] at hσ
  · simp [firstSel] at hσ
  · simp only [firstSel] at hσ
    by_cases hj : 20 ≤ j ∧ j < 31
    · simp only [hj, and_self, if_true, Option.some.injEq] at hσ
      subst hσ
      have hp := h.pubF (j - 20) (by omega)
      have hj3 : ¬ j < 3 := by omega
      have hj42 : 20 ≤ j ∧ j < 42 := ⟨hj.1, by omega⟩
      simp only [varVal, Env309.toSourceEnv, gather309, CorrectedFinalTypedEnv.toSourceEnv,
        gatherCorrectedFinalTypedEnv, dif_neg hj3, dif_pos hj42, envAt, envOfTrace]
      rw [show 20 + (j - 20) = j by omega] at hp
      simp only [show (20 : ℕ) + (j - 20) = j by omega, hp]
      split_ifs <;> simp_all <;> omega
    · simp [hj] at hσ

theorem matches_last_of (h : RowHyps P t Qc) (Q : Fin 309 → F[X])
    (hs : ∀ j, j < 11 → (envAt P t Q (rowL P)).trace j =
      if j = (rowIdx P Qc (rowL P) : ℕ) then 1 else 0) :
    Matches (lastSel (rowIdx P Qc (rowL P)))
      (gather309 P.optimized.basis (envAt P t Q (rowL P))).toSourceEnv := by
  have hcur := matches_curSel_of P.optimized.basis hs
  intro k j v hσ
  cases k
  · exact hcur .traceCur j v (by simpa [lastSel, curSel] using hσ)
  · simp [lastSel] at hσ
  · simp [lastSel] at hσ
  · simp only [lastSel] at hσ
    by_cases hj : 31 ≤ j ∧ j < 42
    · simp only [hj, and_self, if_true, Option.some.injEq] at hσ
      subst hσ
      have hp := h.pubL (j - 31) (by omega)
      have hj3 : ¬ j < 3 := by omega
      have hj42 : 20 ≤ j ∧ j < 42 := ⟨by omega, hj.2⟩
      simp only [varVal, Env309.toSourceEnv, gather309, CorrectedFinalTypedEnv.toSourceEnv,
        gatherCorrectedFinalTypedEnv, dif_neg hj3, dif_pos hj42, envAt, envOfTrace]
      rw [show 31 + (j - 31) = j by omega] at hp
      simp only [show (20 : ℕ) + (j - 20) = j by omega, hp]
      split_ifs <;> simp_all <;> omega
    · simp [hj] at hσ

/-- The hosted initial overlay of the re-hosted first row is the 309 walk column. -/
theorem initial_overlay_eq (h : RowHyps P t Qc) (c : Fin 2) :
    (initialOverlayCoord c).eval (S303 P t Qc (row0 P)) =
      (S309 P t Qc (row0 P)).trace (303 + 3 * (c : ℕ)) := by
  rw [eval_of_nf (initial_nf (rowIdx P Qc (row0 P)) c)
    (matches_first_of h _ (sel303 P t Qc h.hone _))]
  exact host_role_S303 P t Qc _ c

/-- The hosted terminal overlay of the re-hosted last row is the 309 walk column. -/
theorem terminal_overlay_eq (h : RowHyps P t Qc) (c : Fin 2) :
    (terminalOverlayCoord c).eval (S303 P t Qc (rowL P)) =
      (S309 P t Qc (rowL P)).trace (303 + 3 * (c : ℕ)) := by
  rw [eval_of_nf (terminal_nf (rowIdx P Qc (rowL P)) c)
    (matches_last_of h _ (sel303 P t Qc h.hone _))]
  exact host_role_S303 P t Qc _ c

theorem S309_mask (h : RowHyps P t Qc) (i : Fin (nC P)) :
    (S309 P t Qc i).trace 11 = (if (i : ℕ) = 0 then 1 else 0) ∧
      (S309 P t Qc i).trace 12 = (if i = rowL P then 1 else 0) := by
  simp only [S309, Env309.toSourceEnv, gather309, CorrectedFinalTypedEnv.toSourceEnv,
    gatherCorrectedFinalTypedEnv, show (11 : ℕ) ≠ 303 by omega, show (11 : ℕ) ≠ 306 by omega,
    show (12 : ℕ) ≠ 303 by omega, show (12 : ℕ) ≠ 306 by omega, if_false,
    dif_pos (show (11 : ℕ) < 13 by omega), dif_pos (show (12 : ℕ) < 13 by omega)]
  refine ⟨?_, ?_⟩
  · rw [h.mask11 i]; split_ifs <;> simp
  · rw [h.mask12 i]; split_ifs <;> simp

/-- **The queue gates at 309 equal the hosted ones on the re-hosted row.** -/
theorem queue_eqH (h : RowHyps P t Qc) (i : Fin (nC P)) :
    queueNonEmpty309.eval (gather309 P.optimized.basis (envAt P t Qc i)) =
        (correctedFinalExtGate packedQueueNonEmptyId).eval
          (gatherCorrectedFinalTypedEnv P.optimized.basis (envAt P t (reHost309 P t Qc) i)) ∧
      queueTiling309.eval (gather309 P.optimized.basis (envAt P t Qc i)) =
        (correctedFinalExtGate packedQueueTilingId).eval
          (gatherCorrectedFinalTypedEnv P.optimized.basis (envAt P t (reHost309 P t Qc) i)) := by
  have hs := diff_small (rowIdx P Qc i)
  have hag := src_agreeH P t Qc i
  have h12 := hag .traceCur 12 hs.2.1
  have h74 := hag .traceCur 74 hs.2.2.1
  have h75 := hag .traceCur 75 hs.2.2.2
  have hov := overlay_cur_eq P t Qc h.hone i 0
  norm_num at hov
  simp only [varVal] at h12 h74 h75
  have hsrc : ∀ e : Expr, noWalkVars e = true →
      e.eval (S303 P t Qc i) =
        e.eval (gatherCorrectedFinalTypedEnv P.optimized.basis
          (envAt P t (reHost309 P t Qc) i)).toSourceEnv :=
    fun e he => eval_toSourceEnv309_of_noWalkVars _ e he
  constructor
  · rw [show queueNonEmpty309 = lowerW walkQueueNonEmpty309 from rfl,
      ← lower309_eval _ _ _ (lower309_some _ lower309_total.2.2.1),
      ← correctedFinalExtGate_eval_source]
    change walkQueueNonEmpty309.eval (S309 P t Qc i) =
      (finalExtTransitionGates.get ⟨76, by simp⟩).eval _
    rw [OptimizedComputeCanonicalSatisfaction.packedQueueNonEmpty_source, ← hsrc _ (by decide)]
    simp only [walkQueueNonEmpty309, walkQueueNonEmpty, Expr.eval, walkInv, walkInvIndex,
      walkInvRole, ext0, finalWalkLine, finalWalkLineIndex, finalWalkLineRole, walkCountCol]
    rw [hov, h12, h74, h75]
  · rw [show queueTiling309 = lowerW walkQueueTiling309 from rfl,
      ← lower309_eval _ _ _ (lower309_some _ lower309_total.2.2.2.1),
      ← correctedFinalExtGate_eval_source]
    change walkQueueTiling309.eval (S309 P t Qc i) =
      (finalExtTransitionGates.get ⟨77, by simp⟩).eval _
    rw [OptimizedComputeCanonicalSatisfaction.packedQueueTiling_source, ← hsrc _ (by decide)]
    simp only [walkQueueTiling309, walkQueueTiling, Expr.eval, ext0, finalWalkLine,
      finalWalkLineIndex, finalWalkLineRole, walkCountCol]
    rw [hov, h12, h74]

end Endpoints


/-! ## 8. The walk endpoints -/

section WalkEndpoints

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} {P : OptimizedFullStrictNockVMROMPackage F K hOrb}
  {t : OptimizedProductionChallengeTuple K F} {Qc : Fin 309 → F[X]}

/-- **The masked-walk endpoints at 309 equal the hosted ones on the re-hosted row.** -/
theorem endpoints_eqH (h : RowHyps P t Qc) (i : Fin (nC P)) :
    finalMaskedWalkCount1_309.eval (S309 P t Qc i) =
        OptimizedComputeFinalTypedLowering.finalMaskedWalkCount1.eval (S303 P t Qc i) ∧
      finalMaskedWalkOut309.eval (S309 P t Qc i) =
        OptimizedComputeFinalTypedLowering.finalMaskedWalkOut.eval (S303 P t Qc i) ∧
      finalMaskedWalkAccInit309.eval (S309 P t Qc i) =
        OptimizedComputeFinalTypedLowering.finalMaskedWalkAccInit.eval (S303 P t Qc i) := by
  have hs := diff_small (rowIdx P Qc i)
  have hag := src_agreeH P t Qc i
  have h11 : (S303 P t Qc i).trace 11 = (S309 P t Qc i).trace 11 := hag .traceCur 11 hs.1
  have h12 : (S303 P t Qc i).trace 12 = (S309 P t Qc i).trace 12 := hag .traceCur 12 hs.2.1
  have h74 : (S303 P t Qc i).trace 74 = (S309 P t Qc i).trace 74 := hag .traceCur 74 hs.2.2.1
  have hp (j : ℕ) : (S303 P t Qc i).pub j = (S309 P t Qc i).pub j :=
    src_pub_eq P.optimized.basis rfl j
  have hmask := S309_mask h i
  have hcmF := eval_eq_of_insensitive _ _ _ (first_labels_insensitive (rowIdx P Qc i)).2.2
    matches_noSel matches_noSel hag
  refine ⟨?_, ?_, ?_⟩
  · simp only [finalMaskedWalkCount1_309, OptimizedComputeFinalTypedLowering.finalMaskedWalkCount1,
      finalOptimizedWalkCount1, Expr.eval, Expr.eval_subst, Trans.walkCount1, Env.ofSubst, tc,
      Trans.pubv, finalWalkInitialSubst309, finalWalkInitialSubst, fixedIsFirst, walkCountCol]
    rw [h11, hp 0, hcmF]
    by_cases hi0 : (i : ℕ) = 0
    · have hi : i = row0 P := Fin.ext hi0
      subst hi
      have hio := initial_overlay_eq h 0
      norm_num at hio
      rw [hio]
    · rw [hmask.1, if_neg hi0]; simp
  · simp only [finalMaskedWalkOut309, OptimizedComputeFinalTypedLowering.finalMaskedWalkOut,
      finalOptimizedWalkOut, Expr.eval, Expr.eval_subst, Trans.walkOut, Env.ofSubst, tc,
      finalWalkTerminalSubst309, finalWalkTerminalSubst, fixedIsLast, walkAccCol]
    rw [h12]
    by_cases hil : i = rowL P
    · subst hil
      have hio := terminal_overlay_eq h 1
      norm_num at hio
      rw [hio]
    · rw [hmask.2, if_neg hil]; simp
  · simp only [finalMaskedWalkAccInit309, OptimizedComputeFinalTypedLowering.finalMaskedWalkAccInit,
      finalOptimizedWalkAccInit, Expr.eval, Expr.eval_subst, Trans.walkAccInit, Env.ofSubst, tc,
      Trans.pubv, finalWalkInitialSubst309, finalWalkInitialSubst, fixedIsFirst, walkAccCol,
      finalWalkLine, finalWalkLineIndex, finalWalkLineRole, ext0]
    rw [h11, hp 0, hp 1, h74]
    by_cases hi0 : (i : ℕ) = 0
    · have hi : i = row0 P := Fin.ext hi0
      subst hi
      have hm303 := matches_first_of h _ (sel303 P t Qc h.hone _)
      have hm309 := matches_first_of h _ (sel309 P t Qc h.hone _)
      have hlab := eval_eq_of_insensitive _ _ _
        (first_labels_insensitive (rowIdx P Qc (row0 P))).1 hm303 hm309 hag
      have hcc := eval_eq_of_insensitive _ _ _
        (first_labels_insensitive (rowIdx P Qc (row0 P))).2.1 hm303 hm309 hag
      have hio := initial_overlay_eq h 1
      norm_num at hio
      rw [hlab, hcc, hio]
    · rw [hmask.1, if_neg hi0]; simp

end WalkEndpoints


/-! ## 9. The obligations, bucket by bucket (`insensitive_all_buckets`) -/

section Buckets

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} {P : OptimizedFullStrictNockVMROMPackage F K hOrb}
  {t : OptimizedProductionChallengeTuple K F} {Qc : Fin 309 → F[X]}

/-- The decoded 309 row (typed). -/
abbrev G309 (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (t : OptimizedProductionChallengeTuple K F) (Qc : Fin 309 → F[X]) (i : Fin (nC P)) :
    Env309 F K :=
  gather309 P.optimized.basis (envAt P t Qc i)
/-- The decoded re-hosted row (typed, deployed decoder). -/
abbrev G303 (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (t : OptimizedProductionChallengeTuple K F) (Qc : Fin 309 → F[X]) (i : Fin (nC P)) :
    CorrectedFinalTypedEnv F K :=
  gatherCorrectedFinalTypedEnv P.optimized.basis (envAt P t (reHost309 P t Qc) i)
/-- The decoded stage-one row (typed, deployed decoder). -/
abbrev Gpre (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (t : OptimizedProductionChallengeTuple K F) (Qc : Fin 309 → F[X]) (i : Fin (nC P)) :
    CorrectedFinalTypedEnv F K :=
  gatherCorrectedFinalTypedEnv P.optimized.basis (envAt P t (preHost309 P Qc) i)

theorem low_eq (i : Fin (nC P)) (c : ℕ) (hc : lowCol c) :
    (envAt P t (reHost309 P t Qc) i).trace c = (envAt P t Qc i).trace c ∧
      (envAt P t (reHost309 P t Qc) i).traceNext c = (envAt P t Qc i).traceNext c := by
  unfold lowCol at hc
  have hR : isResCol c = false := by simp [isResCol]; omega
  have hH : isHostCol c = false := by simp [isHostCol]; omega
  exact ⟨e303_trace_plain P t Qc i c (by omega) hR hH, e303_traceNext P t Qc i c (by omega) hR hH⟩

/-- **Bucket (i), base-field gates on low columns**: base, the 22 equality checks, the two
exponent gates. -/
theorem low_gate_eqH (i : Fin (nC P)) (g : CoeffExpr F) (hg : ∀ c ∈ colsOf g, lowCol c) :
    g.eval (envAt P t (reHost309 P t Qc) i) = g.eval (envAt P t Qc i) :=
  coeff_eval_congr (E₁ := envAt P t (reHost309 P t Qc) i) (E₂ := envAt P t Qc i) rfl rfl g
    fun c hc => low_eq i c (hg c hc)

/-- **Bucket (i), the 99 Form R certificate gates** (columns plain: below `303`, no host, no
residual). -/
theorem good_gate_eqH (i : Fin (nC P)) (g : CoeffExpr F) (hg : Good g) :
    g.eval (envAt P t (reHost309 P t Qc) i) = g.eval (envAt P t Qc i) := by
  refine coeff_eval_congr (E₁ := envAt P t (reHost309 P t Qc) i) (E₂ := envAt P t Qc i) rfl rfl g
    fun c hc => ?_
  obtain ⟨h303, hH, hR⟩ := hg c hc
  exact ⟨e303_trace_plain P t Qc i c (by omega) hR hH, e303_traceNext P t Qc i c (by omega) hR hH⟩

/-- **Bucket (iii)**: an untouched `𝕂` source evaluates identically on the two decoded rows. -/
theorem untouched_eqH (h : RowHyps P t Qc) (i : Fin (nC P)) (e : Expr)
    (hins : Insensitive (curSel (rowIdx P Qc i)) (diffAt (rowIdx P Qc i)) e = true) :
    e.eval (S303 P t Qc i) = e.eval (S309 P t Qc i) :=
  eval_eq_of_insensitive _ _ e hins (matches303 P t Qc h.hone i) (matches309 P t Qc h.hone i)
    (src_agreeH P t Qc i)

theorem ext_eq_of_plainH (i : Fin (nC P)) (r : Fin 63)
    (hr : (r : ℕ) ∉ hostKRoles ∧ (r : ℕ) ≠ 58 ∧ (r : ℕ) ≠ 59) :
    (G303 P t Qc i).extTrace r = (G309 P t Qc i).base.extTrace r ∧
      (G303 P t Qc i).extTraceNext r = (G309 P t Qc i).base.extTraceNext r := by
  have hcols : ∀ k : Fin 3, isResCol (correctedFinalExtCoordIndex r k) = false ∧
      isHostCol (correctedFinalExtCoordIndex r k) = false := by
    intro k
    simp only [hostKRoles, List.mem_cons, List.not_mem_nil, or_false] at hr
    have := r.isLt; have := k.isLt
    simp only [isResCol, isHostCol, correctedFinalExtCoordIndex, hostKRoles, List.mem_cons,
      List.not_mem_nil, or_false, decide_eq_false_iff_not]
    refine ⟨decide_eq_false ?_, ?_⟩ <;> omega
  constructor
  · simp only [G303, G309, gather309, gatherCorrectedFinalTypedEnv]
    apply Finset.sum_congr rfl; intro k _
    rw [e303_trace_plain P t Qc i _ (by simp [correctedFinalExtCoordIndex]; omega) (hcols k).1
      (hcols k).2]
  · simp only [G303, G309, gather309, gatherCorrectedFinalTypedEnv]
    apply Finset.sum_congr rfl; intro k _
    rw [e303_traceNext P t Qc i _ (by simp [correctedFinalExtCoordIndex]; omega) (hcols k).1
      (hcols k).2]

theorem base_eqH (i : Fin (nC P)) (j : Fin 13) :
    (G303 P t Qc i).baseTrace j = (G309 P t Qc i).base.baseTrace j :=
  (low_eq i j (by unfold lowCol; omega)).1

/-- The untouched core gate on the typed rows. -/
theorem core_untouched_evalH (h : RowHyps P t Qc) (i : Fin (nC P)) (g : CorrectedCoreExtGateId)
    (h74 : g.val ≠ 74) (h75 : g.val ≠ 75) (h76 : g.val ≠ 76) (h77 : g.val ≠ 77) :
    (correctedFinalExtGate g).eval (G303 P t Qc i) =
      (correctedFinalExtGate g).eval (G309 P t Qc i).base := by
  have hb : G303 P t Qc i =
      (gather309 P.optimized.basis (envAt P t (reHost309 P t Qc) i)).base := rfl
  rw [hb, ← correctedFinalExtGate_eval_source, ← correctedFinalExtGate_eval_source,
    ← eval_toSourceEnv309_of_noWalkVars _ _
      (finalExtTransitionGates_noWalkVars _ (List.get_mem _ _)),
    ← eval_toSourceEnv309_of_noWalkVars _ _
      (finalExtTransitionGates_noWalkVars _ (List.get_mem _ _))]
  exact untouched_eqH h i (coreSrc g) (untouched_core_insensitive (rowIdx P Qc i) g h74 h75 h76 h77)

/-- Untouched core positions carry the 309 value. -/
theorem coreSem_untouchedH (h : RowHyps P t Qc) (i : Fin (nC P)) (g : CorrectedCoreExtGateId)
    (h74 : g.val ≠ 74) (h75 : g.val ≠ 75) (h76 : g.val ≠ 76) (h77 : g.val ≠ 77) :
    correctedCoreSemanticValue (G303 P t Qc i) g = coreSemValue309 (G309 P t Qc i) g := by
  have h76' : g ≠ packedQueueNonEmptyId := fun h => h76 (by rw [h])
  have h77' : g ≠ packedQueueTilingId := fun h => h77 (by rw [h])
  have h74' : g ≠ packedWalkCountId := fun h => h74 (by rw [h])
  have h75' : g ≠ packedWalkAccId := fun h => h75 (by rw [h])
  have hb12 := base_eqH (t := t) (Qc := Qc) i 12
  have hgate := core_untouched_evalH h i g h74 h75 h76 h77
  simp only [coreSemValue309, h76', h77', if_false, correctedCoreSemanticValue, h74', h75']
  split_ifs with h81 h7273
  · have he60 := (ext_eq_of_plainH (t := t) (Qc := Qc) i 60 ⟨by decide, by decide, by decide⟩).1
    have he32 := (ext_eq_of_plainH (t := t) (Qc := Qc) i 32 ⟨by decide, by decide, by decide⟩).2
    simp only [accAfterChain, CorrectedFinalTypedExpr.eval]
    rw [hb12, he60, he32]
  · simp only [notLastScalar, hb12, hgate]
  · exact hgate

/-- The final and stage-one decoded rows agree on everything the residual sources read. -/
theorem src_pre_agree (i : Fin (nC P)) :
    ∀ q : VarKind × ℕ, resOK303 q = true →
      varVal (S303 P t Qc i) q.1 q.2 =
        varVal (gather309 P.optimized.basis (envAt P t (preHost309 P Qc) i)).toSourceEnv q.1 q.2 := by
  rintro ⟨k, j⟩ hq
  cases k
  · simp only [resOK303, decide_eq_true_eq] at hq
    apply src_trace_congr
    intro c hc
    unfold physOf at hc
    exact (e303_eq_pre P t Qc i c (by simp [isResCol]; omega)).1
  · simp only [resOK303, decide_eq_true_eq] at hq
    apply src_traceNext_congr
    intro c hc
    unfold physOf at hc
    exact (e303_eq_pre P t Qc i c (by simp [isResCol]; omega)).2
  · exact src_chal_eq P.optimized.basis rfl j
  · exact src_pub_eq P.optimized.basis rfl j

/-- The residual source values on the final and the stage-one decoded rows agree. -/
theorem residualSource_pre (i : Fin (nC P)) (j : Fin 2) :
    (correctedFinalResidualSource ⟨j, by omega⟩).eval (G303 P t Qc i) =
      (correctedFinalResidualSource ⟨j, by omega⟩).eval (Gpre P t Qc i) := by
  have hb : ∀ Q, gatherCorrectedFinalTypedEnv P.optimized.basis (envAt P t Q i) =
      (gather309 P.optimized.basis (envAt P t Q i)).base := fun _ => rfl
  fin_cases j
  · show (correctedFinalExtGate packedWalkCountId).eval
        (gatherCorrectedFinalTypedEnv P.optimized.basis (envAt P t (reHost309 P t Qc) i)) =
      (correctedFinalExtGate packedWalkCountId).eval
        (gatherCorrectedFinalTypedEnv P.optimized.basis (envAt P t (preHost309 P Qc) i))
    rw [hb (reHost309 P t Qc), hb (preHost309 P Qc), ← correctedFinalExtGate_eval_source, ← correctedFinalExtGate_eval_source,
      ← eval_toSourceEnv309_of_noWalkVars _ _
        (finalExtTransitionGates_noWalkVars _ (List.get_mem _ _)),
      ← eval_toSourceEnv309_of_noWalkVars _ _
        (finalExtTransitionGates_noWalkVars _ (List.get_mem _ _))]
    apply eval_congr_reads
    intro q hq
    exact src_pre_agree i q (hosted_residual_reads_ok.1 q hq)
  · show (correctedFinalExtGate packedWalkAccId).eval
        (gatherCorrectedFinalTypedEnv P.optimized.basis (envAt P t (reHost309 P t Qc) i)) =
      (correctedFinalExtGate packedWalkAccId).eval
        (gatherCorrectedFinalTypedEnv P.optimized.basis (envAt P t (preHost309 P Qc) i))
    rw [hb (reHost309 P t Qc), hb (preHost309 P Qc), ← correctedFinalExtGate_eval_source, ← correctedFinalExtGate_eval_source,
      ← eval_toSourceEnv309_of_noWalkVars _ _
        (finalExtTransitionGates_noWalkVars _ (List.get_mem _ _)),
      ← eval_toSourceEnv309_of_noWalkVars _ _
        (finalExtTransitionGates_noWalkVars _ (List.get_mem _ _))]
    apply eval_congr_reads
    intro q hq
    exact src_pre_agree i q (hosted_residual_reads_ok.2 q hq)

/-- **The residual pin on the re-hosted row**: the residual role carries the hosted recurrence. -/
theorem residual_identityH (i : Fin (nC P)) (j : Fin 2) :
    (G303 P t Qc i).extTrace ⟨58 + (j : ℕ), by omega⟩ =
      (correctedFinalResidualSource ⟨j, by omega⟩).eval (G303 P t Qc i) := by
  rw [residualSource_pre i j]
  simp only [G303, gatherCorrectedFinalTypedEnv, correctedFinalExtCoordIndex]
  have hc : ∀ k : Fin 3,
      (envAt P t (reHost309 P t Qc) i).trace (13 + 3 * (58 + (j : ℕ)) + k) =
        coord P.optimized.basis
          ((correctedFinalResidualSource ⟨j, by omega⟩).eval (Gpre P t Qc i)) k :=
    fun k => e303_res P t Qc i j k
  simp only [hc]
  exact P.optimized.basis.sum_repr _

end Buckets


/-! ## 10. The per-row obligations of the deployed chip on the re-hosted trace -/

section Obligations

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} {P : OptimizedFullStrictNockVMROMPackage F K hOrb}
  {t : OptimizedProductionChallengeTuple K F} {Qc : Fin 309 → F[X]}

/-- `lowerLeaf e` evaluates at the 309 decoded row as `e` on its source env. -/
theorem lowerLeaf_eval309 (i : Fin (nC P)) (e : Expr) (hs : (correctedLowerFinal e).isSome)
    (hw : noWalkVars e = true) :
    (lowerLeaf e).eval (G309 P t Qc i) = e.eval (S309 P t Qc i) := by
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp hs
  simp only [lowerLeaf, WTyped.eval, ht', Option.getD_some]
  rw [← correctedLowerFinal_eval _ _ _ ht']
  exact (eval_toSourceEnv309_of_noWalkVars _ e hw).symm

/-- A lowered deployed source evaluates at the re-hosted decoded row as on its source env. -/
theorem lowered_eval303 (i : Fin (nC P)) (e : Expr) (t' : CorrectedFinalTypedExpr)
    (ht' : correctedLowerFinal e = some t') (hw : noWalkVars e = true) :
    t'.eval (G303 P t Qc i) = e.eval (S303 P t Qc i) := by
  rw [← correctedLowerFinal_eval _ _ _ ht']
  exact (eval_toSourceEnv309_of_noWalkVars
    (gather309 P.optimized.basis (envAt P t (reHost309 P t Qc) i)) e hw).symm

/-- **All eight buckets of the deployed chip hold on every re-hosted row** (from the 309
obligations and the row hypotheses). -/
theorem obligations303 (h : RowHyps P t Qc)
    (hob : ∀ i, SourceObligations309 (nC P) (G309 P t Qc i) (envAt P t Qc i))
    (i : Fin (nC P)) :
    CorrectedComputeSourceObligations (nC P) (G303 P t Qc i) (envAt P t (reHost309 P t Qc) i) := by
  have hold := hob i
  have hb12 := base_eqH (t := t) (Qc := Qc) i 12
  have hmask12 : (G309 P t Qc i).base.baseTrace 12 = if i = rowL P then 1 else 0 := h.mask12 i
  -- the 309 walk recurrences vanish off the last row
  have hres_zero : ∀ (hi : (i : ℕ) + 1 < nC P) (j : Fin 2),
      (residualSource309 j).eval (G309 P t Qc i) = 0 := by
    intro hi j
    have hnl : (G309 P t Qc i).base.baseTrace 12 = 0 := by
      rw [hmask12, if_neg]; intro he; have := congrArg Fin.val he; simp at this; omega
    have hcore := hold.extensionCore (if j = 0 then packedWalkCountId else packedWalkAccId)
    have haux := hold.residualAux ⟨j.val, by omega⟩
    have hj2 : (⟨j.val, by omega⟩ : CorrectedResidualWitnessId) ≠ 2 := by
      intro he; have := congrArg Fin.val he; simp at this; omega
    fin_cases j
    · simp [coreSemValue309, correctedCoreSemanticValue, notLastScalar, hnl, packedWalkCountId,
        packedWalkAccId, packedChainId, packedLnChainId, packedWalkLnId, packedQueueNonEmptyId,
        packedQueueTilingId] at hcore
      simp [auxSemValue309, hj2, sub_eq_zero, aux309Idx] at haux
      show WTyped.eval _ (residualSource309 0) = 0
      rw [← haux]; exact hcore
    · simp [coreSemValue309, correctedCoreSemanticValue, notLastScalar, hnl, packedWalkCountId,
        packedWalkAccId, packedChainId, packedLnChainId, packedWalkLnId, packedQueueNonEmptyId,
        packedQueueTilingId] at hcore
      simp [auxSemValue309, hj2, sub_eq_zero, aux309Idx] at haux
      show WTyped.eval _ (residualSource309 1) = 0
      rw [← haux]; exact hcore
  -- the hosted residual source at the re-hosted row is the 309 recurrence
  have hhost : ∀ (hi : (i : ℕ) + 1 < nC P) (j : Fin 2),
      (correctedFinalResidualSource ⟨j, by omega⟩).eval (G303 P t Qc i) =
        (residualSource309 j).eval (G309 P t Qc i) := by
    intro hi j
    have hsteps := walk_steps_eqH P t Qc h.hone i hi
    have hb : G303 P t Qc i =
        (gather309 P.optimized.basis (envAt P t (reHost309 P t Qc) i)).base := rfl
    fin_cases j
    · show (correctedFinalExtGate packedWalkCountId).eval _ = (lowerW walkCountStep309).eval _
      rw [← lower309_eval _ _ _ (lower309_some _ lower309_total.1), hb,
        ← correctedFinalExtGate_eval_source,
        ← eval_toSourceEnv309_of_noWalkVars _ _
          (finalExtTransitionGates_noWalkVars _ (List.get_mem _ _))]
      exact hsteps.1.symm
    · show (correctedFinalExtGate packedWalkAccId).eval _ = (lowerW walkAccStep309).eval _
      rw [← lower309_eval _ _ _ (lower309_some _ lower309_total.2.1), hb,
        ← correctedFinalExtGate_eval_source,
        ← eval_toSourceEnv309_of_noWalkVars _ _
          (finalExtTransitionGates_noWalkVars _ (List.get_mem _ _))]
      exact hsteps.2.symm
  refine
    { base15 := ?_, extensionCore21 := ?_, residualAux3 := ?_, endpointDegreeTwo2 := ?_,
      endpointDegreeFour1 := ?_, selectorEquality2 := ?_, formR99 := ?_, formRLam := ?_,
      expGates := ?_ }
  · intro g hg
    rw [low_gate_eqH i g (base_gates_lowCols _ g hg)]
    exact hold.base15 g hg
  · intro g
    by_cases h74 : g.val = 74
    · have hg : g = packedWalkCountId := Fin.ext h74
      subst hg
      simp only [correctedCoreSemanticValue, if_true]
      by_cases hi : (i : ℕ) + 1 < nC P
      · rw [show residualWitnessRole 0 = ⟨58 + ((0 : Fin 2) : ℕ), by omega⟩ from rfl,
          residual_identityH i 0, hhost hi 0, hres_zero hi 0, mul_zero]
      · have hl : i = rowL P := by apply Fin.ext; simp; omega
        rw [notLastScalar, hb12, hmask12, if_pos hl]
        simp
    by_cases h75 : g.val = 75
    · have hg : g = packedWalkAccId := Fin.ext h75
      subst hg
      simp only [correctedCoreSemanticValue, packedWalkCountId, Fin.mk.injEq,
        show (75 : ℕ) ≠ 74 by omega, if_false, if_true]
      by_cases hi : (i : ℕ) + 1 < nC P
      · rw [show residualWitnessRole 1 = ⟨58 + ((1 : Fin 2) : ℕ), by omega⟩ from rfl,
          residual_identityH i 1, hhost hi 1, hres_zero hi 1, mul_zero]
      · have hl : i = rowL P := by apply Fin.ext; simp; omega
        rw [notLastScalar, hb12, hmask12, if_pos hl]
        simp
    by_cases h76 : g.val = 76
    · have hg : g = packedQueueNonEmptyId := Fin.ext h76
      subst hg
      have hc := hold.extensionCore packedQueueNonEmptyId
      simp only [coreSemValue309, if_true] at hc
      simp only [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId, packedChainId,
        packedLnChainId, packedWalkLnId, packedQueueNonEmptyId, Fin.mk.injEq,
        show (76 : ℕ) ≠ 74 by omega, show (76 : ℕ) ≠ 75 by omega, show (76 : ℕ) ≠ 81 by omega,
        show (76 : ℕ) ≠ 72 by omega, show (76 : ℕ) ≠ 73 by omega, or_self, if_false]
      rw [← (queue_eqH h i).1]; exact hc
    by_cases h77 : g.val = 77
    · have hg : g = packedQueueTilingId := Fin.ext h77
      subst hg
      have hc := hold.extensionCore packedQueueTilingId
      simp only [coreSemValue309, packedQueueTilingId, packedQueueNonEmptyId, Fin.mk.injEq,
        show (77 : ℕ) ≠ 76 by omega, if_false, if_true] at hc
      simp only [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId, packedChainId,
        packedLnChainId, packedWalkLnId, packedQueueTilingId, Fin.mk.injEq,
        show (77 : ℕ) ≠ 74 by omega, show (77 : ℕ) ≠ 75 by omega, show (77 : ℕ) ≠ 81 by omega,
        show (77 : ℕ) ≠ 72 by omega, show (77 : ℕ) ≠ 73 by omega, or_self, if_false]
      rw [← (queue_eqH h i).2]; exact hc
    rw [coreSem_untouchedH h i g h74 h75 h76 h77]
    exact hold.extensionCore g
  · intro j
    by_cases hj : j = 2
    · subst hj
      show correctedAccAfterStep.eval (G303 P t Qc i) = 0
      have hlow := correctedLowerFinal_eval (G303 P t Qc i) _ _ correctedLowerFinal_accAfterStep
      have hlow' := correctedLowerFinal_eval (G309 P t Qc i).base _ _ correctedLowerFinal_accAfterStep
      have e1 : correctedAccAfterStep.eval (G303 P t Qc i) = finalAccAfterStep.eval (S303 P t Qc i) := by
        rw [← hlow]
        exact (eval_toSourceEnv309_of_noWalkVars
          (gather309 P.optimized.basis (envAt P t (reHost309 P t Qc) i)) finalAccAfterStep
          untouched_noWalk.1).symm
      have e2 : correctedAccAfterStep.eval (G309 P t Qc i).base =
          finalAccAfterStep.eval (S309 P t Qc i) := by
        rw [← hlow']
        exact (eval_toSourceEnv309_of_noWalkVars
          (gather309 P.optimized.basis (envAt P t Qc i)) finalAccAfterStep
          untouched_noWalk.1).symm
      rw [e1, untouched_eqH h i _ (untouched_endpoint_insensitive _ _ (by simp)), ← e2]
      have := hold.residualAux 2
      simpa [auxSemValue309, correctedAuxSemanticValue] using this
    · have hj' : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by
        have := j.isLt; have : (j : ℕ) ≠ 2 := fun h' => hj (Fin.ext h'); omega
      simp only [correctedAuxSemanticValue, if_neg hj, sub_eq_zero]
      rcases hj' with hj0 | hj1
      · have e : j = 0 := Fin.ext hj0
        subst e
        exact residual_identityH i 0
      · have e : j = 1 := Fin.ext hj1
        subst e
        exact residual_identityH i 1
  · intro t' ht'
    have hold2 := hold.endpointDegreeTwo
    have hEp := endpoints_eqH h i
    have hins := untouched_endpoint_insensitive (rowIdx P Qc i)
    have hmem : WTyped.leaf t' ∈ correctedEndpoint2.map WTyped.leaf := List.mem_map_of_mem ht'
    rw [endpoint2_309_untouched] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    have hleaf : ∀ e, (correctedLowerFinal e).isSome → noWalkVars e = true →
        WTyped.leaf t' = lowerLeaf e → t'.eval (G303 P t Qc i) = e.eval (S303 P t Qc i) := by
      intro e hs hw hte
      obtain ⟨t'', ht''⟩ := Option.isSome_iff_exists.mp hs
      simp only [lowerLeaf, ht'', Option.getD_some, WTyped.leaf.injEq] at hte
      rw [hte]
      exact lowered_eval303 i e _ ht'' hw
    rcases hmem with hm | hm | hm | hm | hm | hm
    · rw [hleaf _ lowerLeaf_total.1 untouched_noWalk.2.1 hm,
        untouched_eqH h i _ (hins _ (by simp)),
        ← lowerLeaf_eval309 i _ lowerLeaf_total.1 untouched_noWalk.2.1]
      exact hold2 _ (by simp [endpoint2_309])
    · rw [hleaf _ (by decide) untouched_noWalk.2.2.2.2.2.1 hm, ← hEp.1]
      show finalMaskedWalkCount1_309.eval (G309 P t Qc i).toSourceEnv = 0
      rw [lower309_eval _ _ _ (lower309_some _ lower309_total.2.2.2.2.1)]
      exact hold2 _ (by simp [endpoint2_309])
    · rw [hleaf _ (by decide) untouched_noWalk.2.2.2.2.2.2.1 hm, ← hEp.2.1]
      show finalMaskedWalkOut309.eval (G309 P t Qc i).toSourceEnv = 0
      rw [lower309_eval _ _ _ (lower309_some _ lower309_total.2.2.2.2.2.1)]
      exact hold2 _ (by simp [endpoint2_309])
    · rw [hleaf _ lowerLeaf_total.2.1 untouched_noWalk.2.2.1 hm,
        untouched_eqH h i _ (hins _ (by simp)),
        ← lowerLeaf_eval309 i _ lowerLeaf_total.2.1 untouched_noWalk.2.2.1]
      exact hold2 _ (by simp [endpoint2_309])
    · rw [hleaf _ lowerLeaf_total.2.2.1 untouched_noWalk.2.2.2.1 hm,
        untouched_eqH h i _ (hins _ (by simp)),
        ← lowerLeaf_eval309 i _ lowerLeaf_total.2.2.1 untouched_noWalk.2.2.2.1]
      exact hold2 _ (by simp [endpoint2_309])
    · rw [hleaf _ lowerLeaf_total.2.2.2 untouched_noWalk.2.2.2.2.1 hm,
        untouched_eqH h i _ (hins _ (by simp)),
        ← lowerLeaf_eval309 i _ lowerLeaf_total.2.2.2 untouched_noWalk.2.2.2.2.1]
      exact hold2 _ (by simp [endpoint2_309])
  · intro t' ht'
    have hs : (correctedLowerFinal OptimizedComputeFinalTypedLowering.finalMaskedWalkAccInit).isSome :=
      by decide
    obtain ⟨t'', ht''⟩ := Option.isSome_iff_exists.mp hs
    have hc4 : correctedEndpoint4 = [t''] := by
      simp only [correctedEndpoint4, List.filterMap_cons, List.filterMap_nil, ht'']
    rw [hc4] at ht'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht'
    subst ht'
    rw [lowered_eval303 i _ _ ht'' untouched_noWalk.2.2.2.2.2.2.2, ← (endpoints_eqH h i).2.2]
    show finalMaskedWalkAccInit309.eval (G309 P t Qc i).toSourceEnv = 0
    rw [lower309_eval _ _ _ (lower309_some _ lower309_total.2.2.2.2.2.2)]
    exact hold.endpointDegreeFour _ (by simp [endpoint4_309])
  · intro g hg
    rw [low_gate_eqH i g (equality_lowCols g hg)]
    exact hold.selectorEquality2 g hg
  · intro g hg
    rw [good_gate_eqH i g (formR_good g hg)]
    exact hold.formR99 g hg
  · intro t' ht'
    have hc : ∀ c, lowCol c → (envAt P t (reHost309 P t Qc) i).trace c = (envAt P t Qc i).trace c :=
      fun c hc => (low_eq i c hc).1
    have hcn : ∀ c, lowCol c →
        (envAt P t (reHost309 P t Qc) i).traceNext c = (envAt P t Qc i).traceNext c :=
      fun c hc => (low_eq i c hc).2
    rw [typed_eval_congr_noExt (a := G303 P t Qc i) (c := (G309 P t Qc i).base) ?_ ?_ rfl rfl rfl
      ?_ ?_ ?_ t' (formRLamPins_noExt t' ht')]
    · exact hold.formRLam t' ht'
    · funext j; exact hc j (by unfold lowCol; have := j.isLt; omega)
    · funext j; exact hcn j (by unfold lowCol; have := j.isLt; omega)
    · funext j; exact hc _ (by unfold lowCol; have := j.isLt; omega)
    · funext j
      simp only [G303, G309, gather309, gatherCorrectedFinalTypedEnv]
      apply Finset.sum_congr rfl; intro k _
      rw [hc (296 + 3 * (j : ℕ) + (k : ℕ)) (by unfold lowCol; have := j.isLt; have := k.isLt; omega)]
    · exact hc 302 (by unfold lowCol; omega)
  · intro g hg
    rw [low_gate_eqH i g (exp_lowCols g hg)]
    exact hold.expGates g hg

end Obligations


/-! ## 11. **`insensitive_all_buckets`**, `rowHyps_of_sat`, **`satisfies303_of_309`** -/


theorem insensitive_all_buckets {F : Type} [Field F] [DecidableEq F] :
    (∀ n, ∀ g ∈ finalBaseTransitionGates (F := F) n, ∀ c ∈ colsOf g, lowCol c) ∧
    (∀ g ∈ finalEndpointEqualityChecks (F := F), ∀ c ∈ colsOf g, lowCol c) ∧
    (∀ g ∈ computeExpGates (F := F), ∀ c ∈ colsOf g, lowCol c) ∧
    (∀ g ∈ OptimizedComputeRangeCertificate.formRCertificateGates (F := F), Good g) ∧
    (∀ t ∈ formRLamPins, noExtT t = true) ∧
    (∀ s : Fin 11, ∀ i : Fin 82, i.val ≠ 74 → i.val ≠ 75 → i.val ≠ 76 → i.val ≠ 77 →
      Insensitive (curSel s) (diffAt s) (coreSrc i) = true) ∧
    (∀ s : Fin 11, ∀ e ∈ [finalAccAfterStep, OptimizedComputeFinalTypedLowering.finalMaskedWalkLn1,
        finalAccInit, finalAccTerminal, finalLnInit],
      Insensitive (curSel s) (diffAt s) e = true) ∧
    (∀ s' : Fin 11,
      Insensitive (nextSel s') (diffNext s') (ComputeWalkLabel.labelRLC ComputeWalkLabel.nextReader) = true ∧
      Insensitive (nextSel s') (diffNext s')
        (ComputeWalkLabel.childSumCC ComputeWalkLabel.nextReader) = true ∧
      Insensitive noSel (diffNext s') (ComputeWalkLabel.selectorCM ComputeWalkLabel.nextReader) = true) ∧
    (∀ s : Fin 11,
      Insensitive (firstSel s) (diffAt s) (ComputeWalkLabel.labelRLC ComputeWalkLabel.firstReader) = true ∧
      Insensitive (firstSel s) (diffAt s)
        (ComputeWalkLabel.childSumCC ComputeWalkLabel.firstReader) = true ∧
      Insensitive noSel (diffAt s) (ComputeWalkLabel.selectorCM ComputeWalkLabel.firstReader) = true) ∧
    (∀ s : Fin 11, ∀ c : Fin 2,
      simp0 (specSel (curSel s) (overlayCoord .traceCur c)) =
        .Mul (.Const 1) (.Var .traceCur (13 + 3 * overlayANat (stOfIdx s) + c)) ∧
      simp0 (specSel (nextSel s) (overlayCoord .traceNext c)) =
        .Mul (.Const 1) (.Var .traceNext (13 + 3 * overlayANat (stOfIdx s) + c)) ∧
      simp0 (specSel (firstSel s) (initialOverlayCoord c)) =
        .Mul (.Const 1) (.Var .traceCur (13 + 3 * overlayANat (stOfIdx s) + c)) ∧
      simp0 (specSel (lastSel s) (terminalOverlayCoord c)) =
        .Mul (.Const 1) (.Var .traceCur (13 + 3 * overlayANat (stOfIdx s) + c))) ∧
    ((∀ q ∈ readsE (coreSrc ⟨74, by omega⟩), resOK303 q = true) ∧
      (∀ q ∈ readsE (coreSrc ⟨75, by omega⟩), resOK303 q = true)) :=
  ⟨fun n => base_gates_lowCols n, equality_lowCols, exp_lowCols, formR_good, formRLamPins_noExt,
    untouched_core_insensitive, untouched_endpoint_insensitive, next_labels_insensitive,
    first_labels_insensitive,
    fun s c => ⟨overlay_nf_cur s c, overlay_nf_next s c, initial_nf s c, terminal_nf s c⟩,
    hosted_residual_reads_ok⟩

section Assembly

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (t : OptimizedProductionChallengeTuple K F) (Qc : Fin 309 → F[X])

theorem hcharF (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    ∀ m : ℕ, m ≤ 11 → (m : F) = 1 → m = 1 := by
  intro m hm h
  apply DeployedComputeRows.pkgHchar P m hm
  have := congrArg (algebraMap F K) h
  simpa using this

/-- **The row hypotheses and the 309 obligations from acceptance at the 309 chip.** -/
theorem rowHyps_of_sat
    (hsat : RAP.SatisfiesWithPreprocessing (pkgComputeChipAt309 P t) Qc) :
    RowHyps P t Qc ∧ ∀ i, SourceObligations309 (nC P) (G309 P t Qc i) (envAt P t Qc i) := by
  obtain ⟨hbind, hall⟩ := (satisfies309_iff_sourceLanguage P.optimized.family.problem.cfg.compRows_pos
    P.optimized.computeNodes P.optimized.basis (computeChalValOfTuple P.optimized.basis t)
    (P.familyComputePublic t) P.optimized.orbit Qc).1 hsat
  have hob : ∀ i, SourceObligations309 (nC P) (G309 P t Qc i) (envAt P t Qc i) := fun i =>
    hall _ (by simp [rowNodeSet])
  have h11 : Qc ⟨11, by omega⟩ = Nock.Framework.firstRowMask P.optimized.computeNodes :=
    hbind ⟨0, by show 0 < 2; omega⟩
  have h12 : Qc ⟨12, by omega⟩ =
      Nock.Framework.lastRowMask P.optimized.family.problem.cfg.compRows_pos
        P.optimized.computeNodes := hbind ⟨1, by show 1 < 2; omega⟩
  have hone : OneHotRows P Qc := by
    intro i
    apply rowIdx_spec
    obtain ⟨s, hs⟩ := selectors_oneHot (nC P) (envAt P t Qc i) (hob i).base15 (hcharF P)
    refine ⟨s, fun j hj => ?_⟩
    have := hs j hj
    simp only [envAt, envOfTrace, dif_pos (show j < 309 by omega)] at this
    simp only [selAt, dif_pos (show j < 309 by omega)]
    exact this
  have hm11 : ∀ i, (envAt P t Qc i).trace 11 = if (i : ℕ) = 0 then 1 else 0 := by
    intro i
    simp only [envAt, envOfTrace, dif_pos (show (11 : ℕ) < 309 by omega)]
    rw [h11, Nock.Framework.firstRowMask_eval _ P.optimized.computeNodes_injective]
  have hm12 : ∀ i, (envAt P t Qc i).trace 12 = if i = rowL P then 1 else 0 := by
    intro i
    simp only [envAt, envOfTrace, dif_pos (show (12 : ℕ) < 309 by omega)]
    rw [h12, Nock.Framework.lastRowMask_eval _ _ P.optimized.computeNodes_injective]
  have hpub : ∀ (i : Fin (nC P)) (mask : CoeffExpr F) (base : ℕ),
      mask.eval (envAt P t Qc i) = 1 →
      (∀ j, j < 11 → endpointEqualityCheck mask base j ∈ finalEndpointEqualityChecks (F := F)) →
      ∀ j, j < 11 → P.familyComputePublic t (base + j) =
        if j = (rowIdx P Qc i : ℕ) then 1 else 0 := by
    intro i mask base hmask hmem j hj
    have hg := (hob i).selectorEquality2 _ (hmem j hj)
    simp only [endpointEqualityCheck, CoeffExpr.eval, hmask, one_mul, sub_eq_zero] at hg
    have hs := sel309 P t Qc hone i j hj
    simp only [envAt, envOfTrace] at hg hs
    rw [← hs]; exact hg.symm
  refine ⟨⟨hone, hm11, hm12, ?_, ?_⟩, hob⟩
  · refine hpub (row0 P) isFirstVar 20 ?_ ?_
    · simp only [isFirstVar, bv, CoeffExpr.eval]; rw [hm11]; simp
    · intro j hj; simp [finalEndpointEqualityChecks]; exact Or.inl ⟨j, hj, rfl⟩
  · refine hpub (rowL P) isLastVar 31 ?_ ?_
    · simp only [isLastVar, bv, CoeffExpr.eval]; rw [hm12]; simp
    · intro j hj; simp [finalEndpointEqualityChecks]; exact Or.inr ⟨j, hj, rfl⟩

omit [Fintype F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
/-- The deployed obligations read the base environment only below column `303`. -/
theorem obligations_congr {n : ℕ} (b : Module.Basis (Fin 3) F K) {E E' : Env F}
    (htr : ∀ c, c < 303 → E.trace c = E'.trace c) (htn : ∀ c, c < 303 → E.traceNext c = E'.traceNext c)
    (hc : E.chal = E'.chal) (hp : E.pub = E'.pub)
    (h : CorrectedComputeSourceObligations n (gatherCorrectedFinalTypedEnv b E) E) :
    CorrectedComputeSourceObligations n (gatherCorrectedFinalTypedEnv b E') E' := by
  have hg : gatherCorrectedFinalTypedEnv b E = gatherCorrectedFinalTypedEnv b E' := by
    simp only [gatherCorrectedFinalTypedEnv, hc, hp]
    congr 1
    · funext i; exact htr i (by omega)
    · funext i; exact htn i (by omega)
    · funext i; apply Finset.sum_congr rfl; intro k _
      rw [htr _ (by simp [correctedFinalExtCoordIndex]; omega)]
    · funext i; apply Finset.sum_congr rfl; intro k _
      rw [htn _ (by simp [correctedFinalExtCoordIndex]; omega)]
    · funext i; exact htr _ (by omega)
    · funext i; apply Finset.sum_congr rfl; intro k _
      rw [htr _ (by have := i.isLt; have := k.isLt; omega)]
    · funext i; exact htn _ (by omega)
    · funext i; apply Finset.sum_congr rfl; intro k _
      rw [htn _ (by have := i.isLt; have := k.isLt; omega)]
    · exact htr 302 (by omega)
    · exact htn 302 (by omega)
  have hcol : ∀ g : CoeffExpr F, (∀ c ∈ colsOf g, c < 303) → g.eval E' = g.eval E := fun g hgc =>
    coeff_eval_congr (E₁ := E') (E₂ := E) hc.symm hp.symm g fun c hc' =>
      ⟨(htr c (hgc c hc')).symm, (htn c (hgc c hc')).symm⟩
  have hlow : ∀ c, lowCol c → c < 303 := fun c hc' => by unfold lowCol at hc'; omega
  rw [← hg]
  refine
    { base15 := fun g hg' => by
        rw [hcol g fun c hc' => hlow c (base_gates_lowCols _ g hg' c hc')]; exact h.base15 g hg'
      extensionCore21 := h.extensionCore21
      residualAux3 := h.residualAux3
      endpointDegreeTwo2 := h.endpointDegreeTwo2
      endpointDegreeFour1 := h.endpointDegreeFour1
      selectorEquality2 := fun g hg' => by
        rw [hcol g fun c hc' => hlow c (equality_lowCols g hg' c hc')]; exact h.selectorEquality2 g hg'
      formR99 := fun g hg' => by
        rw [hcol g fun c hc' => (formR_good g hg' c hc').1]; exact h.formR99 g hg'
      formRLam := h.formRLam
      expGates := fun g hg' => by
        rw [hcol g fun c hc' => hlow c (exp_lowCols g hg' c hc')]; exact h.expGates g hg' }

/-- **`satisfies303_of_309`.**  Acceptance of the 309 trace `Qc` by the un-hosted chip
at a tuple gives acceptance of the re-hosted trace `reHost P t Qc` by the deployed 303 chip at the
same tuple (`P.computeChipAt t`, its family width). -/
theorem satisfies303_of_309
    (hsat : RAP.SatisfiesWithPreprocessing (pkgComputeChipAt309 P t) Qc) :
    RAP.SatisfiesWithPreprocessing (P.computeChipAt t)
      (FamilyEnvCore.familyQc P.optimized t (reHost P t Qc)) := by
  obtain ⟨hrows, hob⟩ := rowHyps_of_sat P t Qc hsat
  have hbind := hsat.2
  show RAP.SatisfiesWithPreprocessing
    (ProductionNamedComputeRAP P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
      P.optimized.basis (computeChalValOfTuple P.optimized.basis t) (P.familyComputePublic t)
      P.optimized.orbit) _
  erw [productionNamedComputeRAP_satisfies_iff_sourceLanguage]
  refine ⟨?_, ?_⟩
  · intro j
    have hb := hbind j
    fin_cases j
    · change Qc ⟨11, by omega⟩ = _
      exact hb
    · change Qc ⟨12, by omega⟩ = _
      exact hb
  · intro x hx
    obtain ⟨i, _, rfl⟩ :=
      (@Finset.mem_image _ _ (fun a b => Classical.propDecidable (a = b)) _ Finset.univ _).mp hx
    have h303 := obligations303 hrows hob i
    have hw : P.computeChip.rap.w = 303 := PartAStaged.computeWidth303 P
    have htr : ∀ c, c < 303 → (envAt P t (reHost309 P t Qc) i).trace c =
        (envOfTrace (FamilyEnvCore.familyQc P.optimized t (reHost P t Qc)) P.optimized.orbit.ω
          (P.optimized.computeNodes i) (computeChalValOfTuple P.optimized.basis t)
          (P.familyComputePublic t)).trace c := by
      intro c hc
      rw [FamilyEnvCore.familyQc_envTrace]
      simp only [envAt, envOfTrace, dif_pos (show c < 309 by omega)]
      rw [dif_pos (show c < P.computeChip.rap.w by omega)]
      rfl
    have htn : ∀ c, c < 303 → (envAt P t (reHost309 P t Qc) i).traceNext c =
        (envOfTrace (FamilyEnvCore.familyQc P.optimized t (reHost P t Qc)) P.optimized.orbit.ω
          (P.optimized.computeNodes i) (computeChalValOfTuple P.optimized.basis t)
          (P.familyComputePublic t)).traceNext c := by
      intro c hc
      rw [FamilyEnvCore.familyQc_envTraceNext]
      simp only [envAt, envOfTrace, dif_pos (show c < 309 by omega)]
      rw [dif_pos (show c < P.computeChip.rap.w by omega)]
      rfl
    exact obligations_congr P.optimized.basis htr htn rfl rfl h303

end Assembly

end

end Nock.NockVMROM.Thm54.PartAReHost
