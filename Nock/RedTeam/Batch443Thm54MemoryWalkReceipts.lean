/-
  Nock/RedTeam/Batch443Thm54MemoryWalkReceipts.lean

  **Receipts at the in-gate memory chip.**

  * §A — `Batch439`'s census at the committed list: no committed gate reads a host role.
  * §B — **hostile** `memory_label_rlc_is_decoded_label`: on any one-hot successor row,
    `cur(i+1) = RLC^{chal 7}(x^mem of the decoded successor row)` — no honesty hypothesis.
  * §D — **compiled rejection of a concrete hostile trace at `memoryChipAt c`**: for ANY trace
    the family chip accepts and any non-last row `i`, the trace with `acc(i+1)` shifted by
    `δ ≠ 0` (`Batch271.perturb`, one role at one row) is REJECTED — the in-gate accumulation
    step at row `i` evaluates to `δ`.
-/
import Nock.NockVMROM.Thm54.MemoryWalkLabel
import Nock.NockVMROM.Thm54.FamilyMemoryRows
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace
import Nock.RedTeam.Batch271Thm54AnchoringReview
import Nock.RedTeam.Batch439Thm54MemoryWalkHostsUnbound
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch443

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MemoryWalkLabel
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Module

/-! ## A. Census at the committed list -/

theorem committed_hosts_unread :
    (paperKGates (K := ℚ) (F := ℚ)).map Batch439.readsHost = List.replicate 49 false :=
  Batch439.committed_hosts_unread

/-! ## B. The decoded successor label -/

section Decoded

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The successor row's `Pub` as the in-gate label reads it: roles `0..14` of `traceNext`
(cells), state `st`; the fields the label does not read are zero. -/
def nextPub (eK : Env K) (st : MState) : Pub K where
  st := st
  pt := ⟨⟨eK.traceNext 0, eK.traceNext 1, eK.traceNext 2⟩, eK.traceNext 3, eK.traceNext 4⟩
  lc := ⟨⟨eK.traceNext 5, eK.traceNext 6, eK.traceNext 7⟩, eK.traceNext 8, eK.traceNext 9⟩
  rc := ⟨⟨eK.traceNext 10, eK.traceNext 11, eK.traceNext 12⟩, eK.traceNext 13, eK.traceNext 14⟩
  lcSt := st
  rcSt := .halt
  mem := ComputeTable.MemRec.zero
  ipre := 0
  icur := 0

/-- The hosted child state tags of the successor row (roles `45`/`46`). -/
def nextTags (eK : Env K) : Fin 2 → K := fun j => eK.traceNext (childTagHostRole j)

theorem nextPub_cellCoord (eK : Env K) (eF : Env F) (st : MState) (k : Fin 5) :
    ((nextReader (F := F)).col k).eval eK eF = cellCoord (nextPub eK st).pt k := by
  fin_cases k <;> rfl

theorem nextPub_childCoord (eK : Env K) (eF : Env F) (st : MState) (j : Fin 2) (k : Fin 5) :
    ((nextReader (F := F)).col (cellBase j + (k : ℕ))).eval eK eF =
      cellCoord (childCell (nextPub eK st) j) k := by
  fin_cases j <;> fin_cases k <;> rfl

theorem nextTags_eval (eK : Env K) (eF : Env F) (j : Fin 2) :
    (childTagHost (nextReader (F := F)) j).eval eK eF = nextTags eK j := rfl

/-- **Hostile: `cur(i+1)` is `RLC^γ` of the decoded successor `x^mem` label.**  Only the
one-hot successor selectors are assumed; `γ` is whatever sits in slot `7`. -/
theorem memory_label_rlc_is_decoded_label (eK : Env K) (eF : Env F) (st : MState)
    (hsel : ∀ st', eF.traceNext (mopCol st') = if st' = st then 1 else 0) :
    (labelRLC (nextReader (F := F))).eval eK eF =
      Walk.rlc (eK.chal 7) (memoryLabelVec (nextPub eK st)) :=
  labelRLC_eval (nextReader (F := F)) eK eF (nextPub eK st) (eK.chal 7) (fun st' => hsel st')
    (nextPub_cellCoord eK eF st) rfl

/-- Hostile: `cc(i+1)` is the one-hot child sum over the decoded successor payloads. -/
theorem memory_childSum_is_decoded (eK : Env K) (eF : Env F) (st : MState)
    (hsel : ∀ st', eF.traceNext (mopCol st') = if st' = st then 1 else 0) :
    (childSumCC (nextReader (F := F))).eval eK eF =
      ∑ l ∈ Finset.Icc 1 (fanoutMem st),
        eK.chal 3 ^ l * Walk.rlc (eK.chal 7) (childVecN (nextPub eK st) (nextTags eK) (l - 1)) :=
  childSumCC_eval (nextReader (F := F)) eK eF (nextPub eK st) (eK.chal 3) (eK.chal 7)
    (nextTags eK) (fun st' => hsel st') (nextPub_childCoord eK eF st) rfl rfl
    (nextTags_eval eK eF)

end Decoded

/-! ## C. -/

section Scaled

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem nextPub_scaleHosts (l : K) (eK : Env K) (st : MState) :
    nextPub (Batch439.scaleHosts l eK) st = nextPub eK st := by
  simp [nextPub, Batch439.scaleHosts]

theorem nextTags_scaleHosts (l : K) (eK : Env K) :
    nextTags (Batch439.scaleHosts l eK) = nextTags eK := by
  funext j
  fin_cases j <;> simp [nextTags, Batch439.scaleHosts, childTagHostRole]

/-- Scaling the surviving hosts moves `walkAccStepInGate` by `(1 − last)·(λ − 1)·(acc' − acc)`:
the in-gate `cur`/`cc` do not scale. -/
theorem walkAccStepInGate_scaleHosts (l : K) (eK : Env K) (eF : Env F) (st : MState)
    (hsel : ∀ st', eF.traceNext (mopCol st') = if st' = st then 1 else 0) :
    (walkAccStepInGate (F := F)).eval (Batch439.scaleHosts l eK) eF =
      (walkAccStepInGate (F := F)).eval eK eF +
        algebraMap F K (1 - eF.trace 5) * ((l - 1) * (eK.traceNext 33 - eK.trace 33)) := by
  rw [walkAccStepInGate_eval, walkAccStepInGate_eval]
  have hL : (labelRLC (nextReader (F := F))).eval (Batch439.scaleHosts l eK) eF =
      (labelRLC (nextReader (F := F))).eval eK eF := by
    rw [memory_label_rlc_is_decoded_label _ _ st hsel, memory_label_rlc_is_decoded_label _ _ st hsel,
      nextPub_scaleHosts]
    rfl
  have hCC : (childSumCC (nextReader (F := F))).eval (Batch439.scaleHosts l eK) eF =
      (childSumCC (nextReader (F := F))).eval eK eF := by
    rw [memory_childSum_is_decoded _ _ st hsel, memory_childSum_is_decoded _ _ st hsel,
      nextPub_scaleHosts, nextTags_scaleHosts]
    rfl
  rw [hL, hCC]
  simp only [Batch439.scaleHosts, lnRole, accRole, countRole]
  norm_num
  ring

theorem scaled_trace_rejected_at_step (l : K) (eK : Env K) (eF : Env F) (st : MState)
    (hsel : ∀ st', eF.traceNext (mopCol st') = if st' = st then 1 else 0)
    (h0 : (walkAccStepInGate (F := F)).eval eK eF = 0)
    (hl : l ≠ 1) (hacc : eK.traceNext 33 ≠ eK.trace 33) (hlast : eF.trace 5 ≠ 1) :
    (walkAccStepInGate (F := F)).eval (Batch439.scaleHosts l eK) eF ≠ 0 := by
  rw [walkAccStepInGate_scaleHosts l eK eF st hsel, h0, zero_add]
  refine mul_ne_zero ?_ (mul_ne_zero (sub_ne_zero.2 hl) (sub_ne_zero.2 hacc))
  rw [_root_.map_ne_zero]
  exact sub_ne_zero.2 (Ne.symm hlast)

end Scaled

/-! ## D. Compiled rejection of a perturbed accepted trace at `memoryChipAt c` -/

section Perturbation

open Nock.RedTeam.Batch271 (perturb perturb_eval perturb_off colShift colShift_role colShift_base
  colShift_role_zero ShiftedRowF gather_cur gather_next_on gather_chal gather_pub)

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
  [CharP K (ringChar K)] [FiniteDimensional F K]

/-- Shift role `33` (`acc`) at row `i₁` by `δ`. -/
def accShift {n : ℕ} (i₁ : Fin n) (δ : K) : ℕ → Fin n → K :=
  fun r i => if r = 33 ∧ i = i₁ then δ else 0

theorem accShift_ne_role {n : ℕ} (i₁ : Fin n) (δ : K) {r : ℕ} (hr : r ≠ 33) (i : Fin n) :
    accShift i₁ δ r i = 0 := by
  simp [accShift, hr]

theorem accShift_ne_row {n : ℕ} (i₁ : Fin n) (δ : K) (r : ℕ) {i : Fin n} (hi : i ≠ i₁) :
    accShift i₁ δ r i = 0 := by
  simp [accShift, hi]

theorem accShift_at {n : ℕ} (i₁ : Fin n) (δ : K) : accShift i₁ δ 33 i₁ = δ := by
  simp [accShift]

theorem colShift_accShift_ge171 (b : Basis (Fin 3) F K) {n : ℕ} (i₁ : Fin n) (δ : K)
    (c : ℕ) (hc : 171 ≤ c) (i : Fin n) : colShift b (accShift i₁ δ) c i = 0 := by
  simp only [colShift, if_pos (show 6 ≤ c by omega)]
  rw [accShift_ne_role _ _ (by omega)]
  simp [coord]

/-- The one-role perturbation is a `ShiftedRowF` of the original row (the `Batch271` shape). -/
theorem shiftedRowF_perturb_acc (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)
    (hinj : Function.Injective nodes) (i₁ : Fin n) (δ : K)
    (Q : Fin 182 → F[X]) (ω : F) (chal pub : ℕ → F) (j : Fin n)
    (hsucc : ∀ (hj : (j : ℕ) + 1 < n), nodes ⟨(j : ℕ) + 1, hj⟩ = nodes j * ω) :
    ShiftedRowF (envOfTrace Q ω (nodes j) chal pub)
      (envOfTrace (perturb nodes (colShift b (accShift i₁ δ)) Q) ω (nodes j) chal pub)
      (colShift b (accShift i₁ δ)) j where
  cur c := by
    simp only [envOfTrace]
    split_ifs with hc
    · exact perturb_eval nodes hinj _ Q ⟨c, hc⟩ j
    · rw [colShift_accShift_ge171 b i₁ δ c (by omega), add_zero]
  next_on hj c := by
    simp only [envOfTrace]
    split_ifs with hc
    · rw [mul_comm, ← hsucc hj]
      exact perturb_eval nodes hinj _ Q ⟨c, hc⟩ ⟨(j : ℕ) + 1, hj⟩
    · rw [colShift_accShift_ge171 b i₁ δ c (by omega), add_zero]
  next_off c h0 := by
    simp only [envOfTrace]
    split_ifs with hc
    · rw [perturb_off nodes _ Q ⟨c, hc⟩ h0]
    · rfl
  chal _ := rfl
  pub _ := rfl

variable {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (i : Fin P.optimized.family.problem.cfg.memRows)
  (hi : (i : ℕ) + 1 < P.optimized.family.problem.cfg.memRows) (δ : K)

/-- **The attack trace**: `Qm` with `acc(i+1)` (role `33` at row `i+1`) shifted by `δ`. -/
noncomputable def accAttack : Fin (P.memoryChipAt c).rap.w → F[X] :=
  perturb P.optimized.memoryNodes
    (colShift P.optimized.basis (accShift (⟨(i : ℕ) + 1, hi⟩ : Fin _) δ)) Qm

theorem projAt_accAttack :
    projAt P c (accAttack P c Qm i hi δ) =
      perturb P.optimized.memoryNodes
        (colShift P.optimized.basis (accShift (⟨(i : ℕ) + 1, hi⟩ : Fin _) δ)) (projAt P c Qm) := by
  funext j
  rfl

theorem shifted_attack_row :
    ShiftedRowF (memoryBaseEnvAt P c (honestQm P c Qm) i)
      (memoryBaseEnvAt P c (honestQm P c (accAttack P c Qm i hi δ)) i)
      (colShift P.optimized.basis (accShift (⟨(i : ℕ) + 1, hi⟩ : Fin _) δ)) i := by
  rw [← envF_eq_base P c Qm i, ← envF_eq_base P c (accAttack P c Qm i hi δ) i, projAt_accAttack]
  exact shiftedRowF_perturb_acc P.optimized.basis P.optimized.memoryNodes
    P.optimized.memoryNodes_injective _ δ (projAt P c Qm) _ _ _ i
    (fun hj => P.optimized.memoryOrbitAligned i hj)

/-- The next-row read of row `i` is row `i+1`'s current read (orbit alignment). -/
theorem baseEnvAt_traceNext (Q : Fin P.memoryChip.rap.w → F[X]) (j : ℕ) :
    (memoryBaseEnvAt P c Q i).traceNext j =
      (memoryBaseEnvAt P c Q ⟨(i : ℕ) + 1, hi⟩).trace j := by
  simp only [memoryBaseEnvAt, envOfTrace]
  rw [P.optimized.memoryOrbitAligned i hi]
  split_ifs <;> simp [mul_comm]

include hi in
/-- The last-row mask at a non-last row is `0` — from the chip's preprocessing binding. -/
theorem baseEnvAt_trace5_not_last
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm) :
    (memoryBaseEnvAt P c (honestQm P c Qm) i).trace 5 = 0 := by
  have hb : projAt P c Qm ⟨5, by norm_num⟩ =
      OptimizedMemoryCanonicalTrace.lastRowMask P.optimized.memoryNodes :=
    (source_sat_at P c Qm hsat).2 ⟨1, by show (1 : ℕ) < 4; norm_num⟩
  rw [← envF_eq_base P c Qm i]
  simp only [envOfTrace]
  rw [dif_pos (by norm_num : (5 : ℕ) < 182), hb,
    OptimizedMemoryCanonicalTrace.lastRowMask_eval _ P.optimized.memoryNodes_injective]
  simp [show (i : ℕ) + 1 ≠ P.optimized.family.problem.cfg.memRows by omega]

/-- **The perturbed trace is REJECTED by `memoryChipAt c`.**  Given any accepted `Qm`, any
non-last row `i`, and `δ ≠ 0`: the in-gate accumulation step at row `i` evaluates to `δ` on the
attack trace (every other operand of the gate is unchanged: `cur(i+1)`/`cc(i+1)` are polynomials
in roles `0..14`, `45`, `46` and the base selectors, none of which the shift touches), so the
committed gate `walkAccStepInGate` fails and `SatisfiesWithPreprocessing` is false. -/
theorem repaired_memory_chip_rejects_acc_shift
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (hchar : MemStateTagChar F) (hδ : δ ≠ 0) :
    ¬ RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (accAttack P c Qm i hi δ) := by
  intro hsat'
  set Qmh := honestQm P c Qm with hQmh
  set Qah := honestQm P c (accAttack P c Qm i hi δ) with hQah
  have hshift := shifted_attack_row P c Qm i hi δ
  -- the committed gate holds on both traces at row `i`
  have hmem : walkAccStepInGate (F := F) ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis := by
    refine List.mem_append_left _ ?_
    change walkAccStepInGate (F := F) ∈ paperKGates (F := F)
    simp [paperKGates, paperKGatesCore, walkGates, walkStepGates]
  have h0 := mixed_at_family P c Qm hsat i _ hmem
  have h1 := mixed_at_family P c (accAttack P c Qm i hi δ) hsat' i _ hmem
  -- the `𝕂` rows are the gathers of the base rows at `memoryCol0`
  have hK0 : memorySourceEnvAt P c Qmh i = gatherEnv P.optimized.basis memoryCol0
      (memoryBaseEnvAt P c Qmh i) := by
    simp only [memorySourceEnvAt, memorySourceTemplate_col0]
  have hK1 : memorySourceEnvAt P c Qah i = gatherEnv P.optimized.basis memoryCol0
      (memoryBaseEnvAt P c Qah i) := by
    simp only [memorySourceEnvAt, memorySourceTemplate_col0]
  rw [hK0] at h0
  rw [hK1] at h1
  set envF := memoryBaseEnvAt P c Qmh i with henvF
  set envF' := memoryBaseEnvAt P c Qah i with henvF'
  set envK := gatherEnv P.optimized.basis memoryCol0 envF with henvK
  set envK' := gatherEnv P.optimized.basis memoryCol0 envF' with henvK'
  have hne : i ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin _) := fun h => by
    have := congrArg Fin.val h; simp at this
  -- row-`i` values are untouched, next-row values are untouched off role `33`
  have hcur : ∀ r, envK'.trace r = envK.trace r := fun r => by
    rw [gather_cur P.optimized.basis _ hshift r, accShift_ne_row _ _ r hne, add_zero]
  have hnext : ∀ r, r ≠ 33 → envK'.traceNext r = envK.traceNext r := fun r hr => by
    rw [gather_next_on P.optimized.basis _ hshift hi r, accShift_ne_role _ _ hr, add_zero]
  have hnext33 : envK'.traceNext 33 = envK.traceNext 33 + δ := by
    rw [gather_next_on P.optimized.basis _ hshift hi 33, accShift_at]
  have hchal : ∀ r, envK'.chal r = envK.chal r := fun r =>
    gather_chal P.optimized.basis _ hshift r
  have hbase5 : envF'.trace 5 = envF.trace 5 := by
    rw [hshift.cur 5, colShift_base _ _ _ (by norm_num), add_zero]
  have hbase154 : envF'.trace 154 = envF.trace 154 := by
    rw [hshift.cur 154]
    have hz : colShift P.optimized.basis
        (accShift (⟨(i : ℕ) + 1, hi⟩ : Fin _) δ) 154 i = 0 := by
      have h154 : (154 : ℕ) = 6 + 3 * 49 + ((⟨1, by decide⟩ : Fin 3) : ℕ) := by norm_num
      rw [h154]
      exact colShift_role_zero P.optimized.basis _ 49 ⟨1, by decide⟩
        (fun _ => accShift_ne_role _ _ (by decide : (49 : ℕ) ≠ 33) _) i
    rw [hz, add_zero]
  have hbaseNext : ∀ st, envF'.traceNext (mopCol st) = envF.traceNext (mopCol st) := fun st => by
    have hlt : mopCol st < 6 := by cases st <;> simp [mopCol]
    rw [hshift.next_on hi (mopCol st), colShift_base _ _ _ hlt, add_zero]
  -- one-hot successor selectors, from row `i+1` of the accepted trace
  obtain ⟨st₁, hone⟩ := baseOneHot_at_family P c Qm hsat ⟨(i : ℕ) + 1, hi⟩ hchar
  have hsel : ∀ st', envF.traceNext (mopCol st') = if st' = st₁ then 1 else 0 := fun st' => by
    rw [henvF, baseEnvAt_traceNext P c i hi]
    exact hone st'
  have hsel' : ∀ st', envF'.traceNext (mopCol st') = if st' = st₁ then 1 else 0 := fun st' => by
    rw [hbaseNext, hsel]
  -- the in-gate operands agree
  have hpubEq : nextPub envK' st₁ = nextPub envK st₁ := by
    simp only [nextPub, hnext 0 (by norm_num), hnext 1 (by norm_num), hnext 2 (by norm_num),
      hnext 3 (by norm_num), hnext 4 (by norm_num), hnext 5 (by norm_num), hnext 6 (by norm_num),
      hnext 7 (by norm_num), hnext 8 (by norm_num), hnext 9 (by norm_num), hnext 10 (by norm_num),
      hnext 11 (by norm_num), hnext 12 (by norm_num), hnext 13 (by norm_num),
      hnext 14 (by norm_num)]
  have htagsEq : nextTags envK' = nextTags envK := by
    funext j
    fin_cases j <;> simp [nextTags, childTagHostRole, hnext 45 (by norm_num), hnext 46 (by norm_num)]
  have hL : (labelRLC (nextReader (F := F))).eval envK' envF' =
      (labelRLC (nextReader (F := F))).eval envK envF := by
    rw [memory_label_rlc_is_decoded_label _ _ st₁ hsel', memory_label_rlc_is_decoded_label _ _ st₁ hsel,
      hpubEq, hchal]
  have hCC : (childSumCC (nextReader (F := F))).eval envK' envF' =
      (childSumCC (nextReader (F := F))).eval envK envF := by
    rw [memory_childSum_is_decoded _ _ st₁ hsel', memory_childSum_is_decoded _ _ st₁ hsel,
      hpubEq, htagsEq, hchal, hchal]
  -- the gate on the attack trace is the gate on the accepted trace plus `(1 − last)·δ`
  have hgate : (walkAccStepInGate (F := F)).eval envK' envF' =
      (walkAccStepInGate (F := F)).eval envK envF + algebraMap F K (1 - envF.trace 5) * δ := by
    rw [walkAccStepInGate_eval, walkAccStepInGate_eval, hL, hCC, hbase5, hbase154]
    simp only [lnRole, accRole, countRole]
    rw [hnext 31 (by norm_num), hnext33, hcur 33, hcur 32]
    ring
  have hlast : envF.trace 5 = 0 := baseEnvAt_trace5_not_last P c Qm i hi hsat
  rw [hgate, h0, hlast, zero_add, sub_zero, map_one, one_mul] at h1
  exact hδ h1

end Perturbation

end Nock.RedTeam.Batch443

#print axioms Nock.RedTeam.Batch443.memory_label_rlc_is_decoded_label
#print axioms Nock.RedTeam.Batch443.scaled_trace_rejected_at_step
#print axioms Nock.RedTeam.Batch443.repaired_memory_chip_rejects_acc_shift
