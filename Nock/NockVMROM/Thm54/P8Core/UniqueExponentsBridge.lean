/-
  Nock/NockVMROM/Thm54/P8Core/UniqueExponentsBridge.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.UniqueExponentsBridge`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/UniqueExponentsBridge.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.FamilyIOChainRouteB
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Nock.NockVMROM.Thm54.UniqueExponentsBridge

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.RedTeam.Batch575 (UniqueExponents)

noncomputable section

section Generic

variable {F K : Type} [Field F] [Field K] [DecidableEq F] {M : ℕ}
variable (envsK : Fin M → Env K) (envsF : Fin M → Env F) (kroots : ℕ)

/-- 1-indexed row `y` is in range, in state `st`, with decoded exponent `e`. -/
def RowAt (st : MemoryTable.MState) (e y : ℕ) : Prop :=
  ∃ hy : y - 1 < M, 1 ≤ y ∧ memRowStateOf (envsF ⟨y - 1, hy⟩) = st ∧
    rowExp envsF ⟨y - 1, hy⟩ = e

/-- The decoded exponent is injective on the rows of state `st`. -/
def ExpInjOn (st : MemoryTable.MState) : Prop :=
  ∀ r r' : Fin M, memRowStateOf (envsF r) = st → memRowStateOf (envsF r') = st →
    rowExp envsF r = rowExp envsF r' → r = r'

theorem rowAt_unique {st : MemoryTable.MState} {e y y' : ℕ} (hinj : ExpInjOn envsF st)
    (h : RowAt envsF st e y) (h' : RowAt envsF st e y') : y = y' := by
  obtain ⟨hy, h1, hs, he⟩ := h
  obtain ⟨hy', h1', hs', he'⟩ := h'
  have hr := congrArg Fin.val (hinj _ _ hs hs' (he.trans he'.symm))
  simp only at hr
  omega

theorem tree_halt_of (i : ℕ) (h : 1 ≤ i ∧ i ≤ M)
    (hs : memRowStateOf (envsF ⟨i - 1, by omega⟩) = .halt) :
    decodedMTreeOfEnvs envsK envsF kroots i = .halt := by
  rw [decodedMTreeOfEnvs, dif_pos h]
  simp only [hs]

theorem tree_decompose_of (i : ℕ) (h : 1 ≤ i ∧ i ≤ M)
    (hs : memRowStateOf (envsF ⟨i - 1, by omega⟩) = .decompose) :
    decodedMTreeOfEnvs envsK envsF kroots i =
      .decompose
        (if i < childIdx envsF kroots i 1 then
          decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i 1) else .halt)
        (if i < childIdx envsF kroots i 2 then
          decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i 2) else .halt) := by
  rw [decodedMTreeOfEnvs, dif_pos h]
  simp only [hs]

theorem tree_read_of (i : ℕ) (h : 1 ≤ i ∧ i ≤ M)
    (hs : memRowStateOf (envsF ⟨i - 1, by omega⟩) = .read_root) :
    decodedMTreeOfEnvs envsK envsF kroots i =
      .read (rowExp envsF ⟨i - 1, by omega⟩)
        (if i < childIdx envsF kroots i 1 then
          decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i 1) else .halt) := by
  rw [decodedMTreeOfEnvs, dif_pos h]
  simp only [hs]

theorem tree_verify_of (i : ℕ) (h : 1 ≤ i ∧ i ≤ M)
    (hs : memRowStateOf (envsF ⟨i - 1, by omega⟩) = .verify_child) :
    decodedMTreeOfEnvs envsK envsF kroots i =
      .verify (rowExp envsF ⟨i - 1, by omega⟩) 0
        (if i < childIdx envsF kroots i 1 then
          decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i 1) else .halt) := by
  rw [decodedMTreeOfEnvs, dif_pos h]
  simp only [hs]

/-- A followed child slot: the subtree's count is the child's (or `0`), with a witness row. -/
theorem child_prop (cnt : MTree K → ℕ) (hhalt : cnt .halt = 0) (st : MemoryTable.MState)
    (e i l : ℕ)
    (hP : i < childIdx envsF kroots i l →
      cnt (decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i l)) ≤ 1 ∧
      (1 ≤ cnt (decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i l)) →
        ∃ y ∈ reachRows envsF kroots (childIdx envsF kroots i l), RowAt envsF st e y)) :
    cnt (if i < childIdx envsF kroots i l then
        decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i l) else .halt) ≤ 1 ∧
    (1 ≤ cnt (if i < childIdx envsF kroots i l then
        decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i l) else .halt) →
      i < childIdx envsF kroots i l ∧
        ∃ y ∈ reachRows envsF kroots (childIdx envsF kroots i l), RowAt envsF st e y) := by
  by_cases hc : i < childIdx envsF kroots i l
  · rw [if_pos hc]
    exact ⟨(hP hc).1, fun h => ⟨hc, (hP hc).2 h⟩⟩
  · rw [if_neg hc, hhalt]
    exact ⟨by omega, fun h => absurd h (by omega)⟩

/-- The two child subtrees of a `decompose` row reach disjoint row sets. -/
theorem sibling_disjoint (i : ℕ) (h : 1 ≤ i ∧ i ≤ M) (hfo : 2 ≤ foOfMem envsF i)
    (hc : i < childIdx envsF kroots i 1) :
    Disjoint (reachRows envsF kroots (childIdx envsF kroots i 1))
      (reachRows envsF kroots (childIdx envsF kroots i 2)) := by
  have h12 : childIdx envsF kroots i 2 = childIdx envsF kroots i 1 + 1 := by
    unfold childIdx; omega
  refine reach_disjoint envsF kroots _ _ (by omega) ?_ ?_
  · intro hm
    have := (reach_bounds envsF kroots _ _ hm).1
    omega
  · intro hm
    have hne : childIdx envsF kroots i 2 ≠ childIdx envsF kroots i 1 := by omega
    obtain ⟨p, hp, l, hl1, hl2, _, heq⟩ := reach_parent envsF kroots _ _ hm hne
    have hb := reach_bounds envsF kroots _ p hp
    have hpi := child_parent_unique envsF kroots hb.2.1 h.1 hl1 hl2
      (by norm_num : 1 ≤ 2) hfo heq.symm
    omega

/-- **The generic count bound.**  For a count `cnt` that charges one per node of class `st₀` at
exponent `e` (and is additive otherwise), every decoded tree has `cnt ≤ 1`, provided the decoded
exponent is injective on the rows of class `st₀`.  Holds at every env tuple. -/
theorem count_le_one_generic (cnt : MTree K → ℕ) (st₀ : MemoryTable.MState) (e : ℕ)
    (hhalt : cnt .halt = 0)
    (hdec : ∀ L R, cnt (.decompose L R) = cnt L + cnt R)
    (hread : ∀ x T, cnt (.read x T) = (if st₀ = .read_root ∧ x = e then 1 else 0) + cnt T)
    (hver : ∀ x (a : K) T,
      cnt (.verify x a T) = (if st₀ = .verify_child ∧ x = e then 1 else 0) + cnt T)
    (hinj : ExpInjOn envsF st₀) :
    ∀ i, cnt (decodedMTreeOfEnvs envsK envsF kroots i) ≤ 1 ∧
      (1 ≤ cnt (decodedMTreeOfEnvs envsK envsF kroots i) →
        ∃ y ∈ reachRows envsF kroots i, RowAt envsF st₀ e y) := by
  refine measure_induction (M := M) _ fun i ih => ?_
  by_cases h : 1 ≤ i ∧ i ≤ M
  · have hfo := foOfMem_eq envsF i h
    have hreach := reach_eq envsF kroots i h
    have hself := self_mem_reach envsF kroots i h
    have hch : ∀ l, _ := fun l =>
      child_prop envsK envsF kroots cnt hhalt st₀ e i l (fun hc => ih _ hc h.1 h.2)
    have hsub1 : 1 ≤ foOfMem envsF i → ∀ y, i < childIdx envsF kroots i 1 →
        y ∈ reachRows envsF kroots (childIdx envsF kroots i 1) → y ∈ reachRows envsF kroots i := by
      intro hf y hc hy
      rw [hreach]
      exact Finset.mem_union.2 (Or.inr (Finset.mem_union.2 (Or.inl (by rw [if_pos ⟨hf, hc⟩]; exact hy))))
    have hsub2 : 2 ≤ foOfMem envsF i → ∀ y, i < childIdx envsF kroots i 2 →
        y ∈ reachRows envsF kroots (childIdx envsF kroots i 2) → y ∈ reachRows envsF kroots i := by
      intro hf y hc hy
      rw [hreach]
      exact Finset.mem_union.2 (Or.inr (Finset.mem_union.2 (Or.inr (by rw [if_pos ⟨hf, hc⟩]; exact hy))))
    rcases hst : memRowStateOf (envsF ⟨i - 1, by omega⟩) with _ | _ | _ | _
    · -- decompose
      have hfo2 : foOfMem envsF i = 2 := by rw [hfo, hst]; rfl
      rw [tree_decompose_of envsK envsF kroots i h hst, hdec]
      obtain ⟨h1le, h1w⟩ := hch 1
      obtain ⟨h2le, h2w⟩ := hch 2
      refine ⟨?_, ?_⟩
      · by_contra hgt
        obtain ⟨hc1, y1, hy1, hr1⟩ := h1w (by omega)
        obtain ⟨hc2, y2, hy2, hr2⟩ := h2w (by omega)
        have hyy := rowAt_unique envsF hinj hr1 hr2
        subst hyy
        exact Finset.disjoint_left.1
          (sibling_disjoint envsF kroots i h (by omega) hc1) hy1 hy2
      · intro hpos
        by_cases hp1 : 1 ≤ cnt (if i < childIdx envsF kroots i 1 then
            decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i 1) else .halt)
        · obtain ⟨hc1, y, hy, hr⟩ := h1w hp1
          exact ⟨y, hsub1 (by omega) y hc1 hy, hr⟩
        · obtain ⟨hc2, y, hy, hr⟩ := h2w (by omega)
          exact ⟨y, hsub2 (by omega) y hc2 hy, hr⟩
    · -- halt
      rw [tree_halt_of envsK envsF kroots i h hst, hhalt]
      exact ⟨by omega, fun h => absurd h (by omega)⟩
    · -- read_root
      have hfo1 : foOfMem envsF i = 1 := by rw [hfo, hst]; rfl
      rw [tree_read_of envsK envsF kroots i h hst, hread]
      obtain ⟨h1le, h1w⟩ := hch 1
      by_cases hown : st₀ = .read_root ∧ rowExp envsF ⟨i - 1, by omega⟩ = e
      · rw [if_pos hown]
        have hri : RowAt envsF st₀ e i := ⟨by omega, h.1, hst.trans hown.1.symm, hown.2⟩
        refine ⟨?_, fun _ => ⟨i, hself, hri⟩⟩
        by_contra hgt
        obtain ⟨hc1, y, hy, hr⟩ := h1w (by omega)
        have hyi := rowAt_unique envsF hinj hr hri
        have := (reach_bounds envsF kroots _ y hy).1
        omega
      · rw [if_neg hown, zero_add]
        refine ⟨h1le, fun hpos => ?_⟩
        obtain ⟨hc1, y, hy, hr⟩ := h1w hpos
        exact ⟨y, hsub1 (by omega) y hc1 hy, hr⟩
    · -- verify_child
      have hfo1 : foOfMem envsF i = 1 := by rw [hfo, hst]; rfl
      rw [tree_verify_of envsK envsF kroots i h hst, hver]
      obtain ⟨h1le, h1w⟩ := hch 1
      by_cases hown : st₀ = .verify_child ∧ rowExp envsF ⟨i - 1, by omega⟩ = e
      · rw [if_pos hown]
        have hri : RowAt envsF st₀ e i := ⟨by omega, h.1, hst.trans hown.1.symm, hown.2⟩
        refine ⟨?_, fun _ => ⟨i, hself, hri⟩⟩
        by_contra hgt
        obtain ⟨hc1, y, hy, hr⟩ := h1w (by omega)
        have hyi := rowAt_unique envsF hinj hr hri
        have := (reach_bounds envsF kroots _ y hy).1
        omega
      · rw [if_neg hown, zero_add]
        refine ⟨h1le, fun hpos => ?_⟩
        obtain ⟨hc1, y, hy, hr⟩ := h1w hpos
        exact ⟨y, hsub1 (by omega) y hc1 hy, hr⟩
  · rw [tree_out envsK envsF kroots i h, hhalt]
    exact ⟨by omega, fun h => absurd h (by omega)⟩

theorem readCount_le_one_of_inj (hinj : ExpInjOn envsF .read_root) (i e : ℕ) :
    readCount e (decodedMTreeOfEnvs envsK envsF kroots i) ≤ 1 :=
  (count_le_one_generic envsK envsF kroots (readCount e) .read_root e
    (by simp [readCount]) (fun L R => by simp [readCount]) (fun x T => by simp [readCount])
    (fun x a T => by simp [readCount]) hinj i).1

theorem verifyCount_le_one_of_inj (hinj : ExpInjOn envsF .verify_child) (i e : ℕ) :
    verifyCount e (decodedMTreeOfEnvs envsK envsF kroots i) ≤ 1 :=
  (count_le_one_generic envsK envsF kroots (verifyCount e) .verify_child e
    (by simp [verifyCount]) (fun L R => by simp [verifyCount]) (fun x T => by simp [verifyCount])
    (fun x a T => by simp [verifyCount]) hinj i).1

/-- **§A's conclusion**: exponent injectivity on both active classes gives `UniqueExponents` for
every decoded tree, at every env tuple. -/
theorem uniqueExponents_of_expInj (hR : ExpInjOn envsF .read_root)
    (hV : ExpInjOn envsF .verify_child) (i : ℕ) :
    UniqueExponents (decodedMTreeOfEnvs envsK envsF kroots i) := fun e =>
  ⟨readCount_le_one_of_inj envsK envsF kroots hR i e,
    verifyCount_le_one_of_inj envsK envsF kroots hV i e⟩

/-- `ExpInjOn` reads only the traces. -/
theorem expInjOn_congr {envsF' : Fin M → Env F} (ht : ∀ r, (envsF r).trace = (envsF' r).trace)
    {st : MemoryTable.MState} (h : ExpInjOn envsF st) : ExpInjOn envsF' st := by
  intro r r' hs hs' he
  have hs1 : memRowStateOf (envsF r) = st := by simpa only [memRowStateOf, ht r] using hs
  have hs1' : memRowStateOf (envsF r') = st := by simpa only [memRowStateOf, ht r'] using hs'
  have he1 : rowExp envsF r = rowExp envsF r' := by simpa only [rowExp, ht r, ht r'] using he
  exact h r r' hs1 hs1' he1

theorem sel2_of_read {E : Env F} (h : memRowStateOf E = .read_root) : E.trace 2 = 1 := by
  unfold memRowStateOf at h
  split_ifs at h with h0 h1 h2
  exact h2

theorem not_sel_of_verify {E : Env F} (h : memRowStateOf E = .verify_child) :
    E.trace 0 ≠ 1 ∧ E.trace 1 ≠ 1 ∧ E.trace 2 ≠ 1 := by
  unfold memRowStateOf at h
  split_ifs at h with h0 h1 h2
  exact ⟨h0, h1, h2⟩

end Generic

section Family

open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open OptimizedStrictPackage
open OptimizedStrictFullPackage
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP
open DeployedChipFamily
open FamilyComputeRows
open FamilyMemoryRows
open FamilyIOChain
open Module
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

/-- **Twin of `Batch521.readRoot_sel_implies_ver1` at the family chip.**  Selector `read_root`
(base column `2`) forces `ver = 1`, at a basis with
`coord b 1 0 ≠ 0`. -/
theorem readSel_ver_at (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (hb1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0) (i : Fin (memRows P))
    (hsel : (memEnvF P c Qm i).trace 2 = 1) : (memEnvK P c Qm i).trace 39 = 1 := by
  have hgate := (row_parts_at P c Qm hsat i).1 (readRootVerGate P.optimized.basis)
    (by simp [baseTransitionGates])
  have heval : (readRootVerGate P.optimized.basis).eval (memEnvF P c Qm i) =
      (memEnvF P c Qm i).trace 2 *
        (coord P.optimized.basis (1 : K) (0 : Fin 3) - (memEnvF P c Qm i).trace (6 + 3 * 39)) := by
    simp [readRootVerGate, CoeffExpr.eval, bcur, extCoord]
  have hcoord : coord P.optimized.basis ((memEnvK P c Qm i).trace 39) (0 : Fin 3) =
      (memEnvF P c Qm i).trace (6 + 3 * 39) := by
    simpa [memEnvK, memorySourceEnvAt, memorySourceTemplate_col0, gatherEnv, memoryCol0] using
      coord_sum_smul P.optimized.basis
        (fun j => (memEnvF P c Qm i).trace (6 + 3 * 39 + (j : ℕ))) (0 : Fin 3)
  change (readRootVerGate P.optimized.basis).eval (memEnvF P c Qm i) = 0 at hgate
  rw [heval, hsel, one_mul, sub_eq_zero] at hgate
  rcases ver_bool_at P c Qm hsat i with h0 | h1
  · exfalso
    apply hb1
    rw [hgate, ← hcoord, h0, coord_zero]
  · exact h1

/-- A `verify_child`-decoded family row has selector `3` set (booleanity + `bsum4`). -/
theorem verify_sel_at (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin (memRows P)) (hst : memRowStateOf (memEnvF P c Qm i) = .verify_child) :
    (memEnvF P c Qm i).trace 3 = 1 := by
  obtain ⟨h0, h1, h2⟩ := not_sel_of_verify hst
  have b0 := selector_zero_or_one_at P c Qm hsat i ⟨0, by decide⟩
  have b1 := selector_zero_or_one_at P c Qm hsat i ⟨1, by decide⟩
  have b2 := selector_zero_or_one_at P c Qm hsat i ⟨2, by decide⟩
  simp only at b0 b1 b2
  have z0 : (memEnvF P c Qm i).trace 0 = 0 := b0.resolve_right h0
  have z1 : (memEnvF P c Qm i).trace 1 = 0 := b1.resolve_right h1
  have z2 : (memEnvF P c Qm i).trace 2 = 0 := b2.resolve_right h2
  have hsum := (row_parts_at P c Qm hsat i).1 (bsum4 .traceCur)
    (by simp [baseTransitionGates, paperBaseGates])
  change (bsum4 (F := F) .traceCur).eval (memEnvF P c Qm i) = 0 at hsum
  simp only [bsum4, CoeffExpr.eval] at hsum
  rw [z0, z1, z2] at hsum
  linear_combination hsum

section Accepted

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hio : FamilyIOGood P c Qc Qm)
  (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K)
  (hb1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0)
include hacc hgood hio hrb hb1

/-- Two selector-`2` family memory rows with one `reqIdx` are one row (route B through `ver`). -/
theorem read_reqIdx_injective_at (i i' : Fin (memRows P))
    (hs : (memEnvF P c Qm i).trace 2 = 1) (hs' : (memEnvF P c Qm i').trace 2 = 1)
    (heq : (memEnvF P c Qm i).trace reqIdxCol = (memEnvF P c Qm i').trace reqIdxCol) :
    i = i' :=
  ver_reqIdx_injective_at P c Qc Qm hacc hgood hio
    (OptimizedHostileConfiguration.hchar_of_package P) (hKp_of_rowsBound_at P hrb)
    (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm) i i'
    (readSel_ver_at P c Qm hacc.memory_satisfies hb1 i hs)
    (readSel_ver_at P c Qm hacc.memory_satisfies hb1 i' hs') heq

omit hb1 in
/-- On a `ver = 1` family row, `natLift reqIdx` determines `reqIdx`. -/
theorem reqIdx_eq_natLift_at (i : Fin (memRows P)) (hver : (memEnvK P c Qm i).trace 39 = 1) :
    (memEnvF P c Qm i).trace reqIdxCol =
      ((RecordCarrier.natLift ((memEnvF P c Qm i).trace reqIdxCol) : ℕ) : F) := by
  obtain ⟨a, j, hact, h1, -, -⟩ :=
    memory_row_bound_at P c Qc Qm hacc hgood hio
      (OptimizedHostileConfiguration.hchar_of_package P) (hKp_of_rowsBound_at P hrb)
      (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm) i hver
  rw [h1, RecordCarrier.natLift_natCast
    (expOfAt_lt_ringChar P c Qc hacc.compute_satisfies
      (OptimizedHostileConfiguration.hchar_of_package P) (hKp_of_rowsBound_at P hrb)
      (hKreq_of_rowsBound_at P c Qc) hact)]

/-- **`read_root` exponent injectivity at the family chip.** -/
theorem expInj_read_at : ExpInjOn (memEnvF P c Qm) .read_root := by
  intro r r' hs hs' he
  have h2 := sel2_of_read hs
  have h2' := sel2_of_read hs'
  have hv := readSel_ver_at P c Qm hacc.memory_satisfies hb1 r h2
  have hv' := readSel_ver_at P c Qm hacc.memory_satisfies hb1 r' h2'
  refine read_reqIdx_injective_at P c Qc Qm hacc hgood hio hrb hb1 r r' h2 h2' ?_
  rw [reqIdx_eq_natLift_at P c Qc Qm hacc hgood hio hrb r hv,
    reqIdx_eq_natLift_at P c Qc Qm hacc hgood hio hrb r' hv']
  unfold rowExp at he
  simp only [reqIdxCol]
  rw [he]

/-- The family read records are nodup. -/
theorem hostileReadsAt_nodup : (hostileReadsAt P c Qm).Nodup := by
  unfold hostileReadsAt
  rw [List.nodup_flatten, List.pairwise_ofFn]
  refine ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
    unfold MemoryInternalPole.rowReadsOf
    split_ifs <;> simp
  · intro i i' hii x hx hx'
    unfold MemoryInternalPole.rowReadsOf at hx hx'
    split_ifs at hx hx' with h2 h2'
    · simp only [List.mem_singleton] at hx hx'
      have h9 := congrFun (hx.symm.trans hx') 9
      have heq : (memEnvF P c Qm i).trace reqIdxCol = (memEnvF P c Qm i').trace reqIdxCol := by
        apply (algebraMap F K).injective
        simpa [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord,
          reqIdxCol] using h9
      exact absurd (read_reqIdx_injective_at P c Qc Qm hacc hgood hio hrb hb1 i i' h2 h2' heq)
        (ne_of_lt hii)
    all_goals simp at hx hx'

omit hio hb1 in
/-- Every selector-`3` family row's record is a selector-`2` row's record (`intermediate`). -/
theorem verify_partner_at (i : Fin (memRows P)) (h3 : (memEnvF P c Qm i).trace 3 = 1) :
    ∃ i'' : Fin (memRows P), (memEnvF P c Qm i'').trace 2 = 1 ∧
      MemoryInternalPole.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i) =
        MemoryInternalPole.rowRecord (memEnvK P c Qm i'') (memEnvF P c Qm i'') := by
  have hperm := paired_records_of_rowsBound_at P c Qc Qm hacc hgood hrb
  have hmem : MemoryInternalPole.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i) ∈
      hostileVerifiesAt P c Qm := by
    simp only [hostileVerifiesAt, List.mem_flatten, List.mem_ofFn]
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    simp [MemoryInternalPole.rowVerifiesOf, h3]
  have hread := (List.Perm.mem_iff hperm).2 hmem
  simp only [hostileReadsAt, List.mem_flatten, List.mem_ofFn] at hread
  obtain ⟨l, ⟨i'', rfl⟩, hl⟩ := hread
  unfold MemoryInternalPole.rowReadsOf at hl
  split_ifs at hl with hr
  · simp only [List.mem_singleton] at hl
    exact ⟨i'', hr, hl⟩
  · simp at hl

/-- **`verify_child` exponent injectivity at the family chip.** -/
theorem expInj_verify_at : ExpInjOn (memEnvF P c Qm) .verify_child := by
  intro r r' hs hs' he
  have hsat := hacc.memory_satisfies
  have h3 := verify_sel_at P c Qm hsat r hs
  have h3' := verify_sel_at P c Qm hsat r' hs'
  obtain ⟨a, ha2, hra⟩ := verify_partner_at P c Qc Qm hacc hgood hrb r h3
  obtain ⟨a', ha2', hra'⟩ := verify_partner_at P c Qc Qm hacc hgood hrb r' h3'
  have hslot : ∀ x y : Fin (memRows P),
      MemoryInternalPole.rowRecord (memEnvK P c Qm x) (memEnvF P c Qm x) =
        MemoryInternalPole.rowRecord (memEnvK P c Qm y) (memEnvF P c Qm y) →
      (memEnvF P c Qm x).trace reqIdxCol = (memEnvF P c Qm y).trace reqIdxCol := by
    intro x y hxy
    have h9 := congrFun hxy 9
    apply (algebraMap F K).injective
    simpa [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord,
      reqIdxCol] using h9
  have hva := readSel_ver_at P c Qm hsat hb1 a ha2
  have hva' := readSel_ver_at P c Qm hsat hb1 a' ha2'
  have hq : (memEnvF P c Qm r).trace reqIdxCol = (memEnvF P c Qm r').trace reqIdxCol := by
    rw [hslot r a hra, hslot r' a' hra',
      reqIdx_eq_natLift_at P c Qc Qm hacc hgood hio hrb a hva,
      reqIdx_eq_natLift_at P c Qc Qm hacc hgood hio hrb a' hva', ← hslot r a hra,
      ← hslot r' a' hra']
    unfold rowExp at he
    simp only [reqIdxCol]
    rw [he]
  have haa : a = a' := read_reqIdx_injective_at P c Qc Qm hacc hgood hio hrb hb1 a a' ha2 ha2'
    (by rw [← hslot r a hra, ← hslot r' a' hra']; exact hq)
  subst haa
  have hrec : MemoryInternalPole.rowRecord (memEnvK P c Qm r) (memEnvF P c Qm r) =
      MemoryInternalPole.rowRecord (memEnvK P c Qm r') (memEnvF P c Qm r') := hra.trans hra'.symm
  have hnd : (hostileVerifiesAt P c Qm).Nodup :=
    (List.Perm.nodup_iff (paired_records_of_rowsBound_at P c Qc Qm hacc hgood hrb)).1
      (hostileReadsAt_nodup P c Qc Qm hacc hgood hio hrb hb1)
  have hx : MemoryInternalPole.rowRecord (memEnvK P c Qm r) (memEnvF P c Qm r) ∈
      MemoryInternalPole.rowVerifiesOf (memEnvF P c Qm r) (memEnvK P c Qm r) := by simp [MemoryInternalPole.rowVerifiesOf, h3]
  have hx' : MemoryInternalPole.rowRecord (memEnvK P c Qm r) (memEnvF P c Qm r) ∈
      MemoryInternalPole.rowVerifiesOf (memEnvF P c Qm r') (memEnvK P c Qm r') := by
    rw [hrec]; simp [MemoryInternalPole.rowVerifiesOf, h3']
  exact eq_of_mem_flatten_ofFn_nodup' _ hnd hx hx'

theorem uniqueExponents_decoded_pkg (kroots i : ℕ) :
    UniqueExponents (decodedMTreeOfEnvs (P.memorySourceEnv (honestQm P c Qm))
      (P.memoryBaseEnv (honestQm P c Qm)) kroots i) := by
  have ht : ∀ r, (memEnvF P c Qm r).trace = (P.memoryBaseEnv (honestQm P c Qm) r).trace :=
    fun r => funext fun j => memEnvF_trace P c Qm r j
  exact uniqueExponents_of_expInj _ _ kroots
    (expInjOn_congr (memEnvF P c Qm) ht (expInj_read_at P c Qc Qm hacc hgood hio hrb hb1))
    (expInjOn_congr (memEnvF P c Qm) ht (expInj_verify_at P c Qc Qm hacc hgood hio hrb hb1)) i

end Accepted

end Family

end

end Nock.NockVMROM.Thm54.UniqueExponentsBridge
