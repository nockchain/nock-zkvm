/-
  Nock/RedTeam/Batch671Thm54ExponentCarrierHonestFill.lean

  **C1 of the THIRTY-FIRST move (lane `exponent-carrier`): the honest fill.**

  * **Compute `S` (`computeExpCol = 302`)**: the canonical trace's column `302` at row `i` is
    `honestS R i` (`canonical_S`), the prefix sum of the request arities:
    `honestS R 0 = 0`, `honestS R (i+1) = honestS R i + arity(state i)` (`honestS_zero`,
    `honestS_step` — `recordCount`, the same count the template's `computeLineAdvance` uses).
  * **The exponent of request `(i, j)` is `S(i) + j + 1`** — its `1`-based position in the
    derived request list (`honest_request_exponent`, `honestExp_activeRequest`).
  * **Memory `reqIdx` (base column `181`)**: the canonical value is `honestReqIdx R i`
    (`canonical_reqIdx`): on a `read_root` / `verify_child` row the exponent of the request the
    row's record answers — `S(i') + j + 1` when the record is the `j`-th active request of compute
    row `i'` (`honest_reqIdx_eq_request_exponent`) — and `0` on every other row
    (`honest_reqIdx_inactive`).  **Duplicate lookups are included**: two rows serving the same record
    get the same `reqIdx` (`honest_reqIdx_duplicate`), because the fill is a function of the record.
  * **The α-free template (`SemanticTimestampSkeleton`, pre-`α`)**: the line exponent of compute row
    `k` is the prefix sum of `recordCount` (`template_lnPrev_eq_prefix`), so the template's
    `recordExponent i = prefix(k) + i + 1` (`template_recordExponent_eq_prefix`) — the same formula
    as the honest fill's `S(i) + j + 1`.  This is the template-level `recordExponent` the carrier
    represents.
-/
import Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
import Nock.NockVMROM.Thm54.SemanticTimestampStrategy

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch671

open Nock Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace
open Nock.NockVMROM.Thm54.StrictExtension
open Module
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [DecidableEq F] {p : ℕ} [CharP K p]
  {R : PlusIOSegmentedFamily F K}

/-! ## A. Compute `S` -/

/-- **The canonical carrier column is the honest prefix sum.** -/
theorem canonical_S (A : SampledIOSameExecutionAssignment R p)
    (hn : 0 < R.problem.cfg.compRows) (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.compRows) :
    (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit ⟨302, by omega⟩).eval
      (nodes i) = ((honestS R i : ℕ) : F) :=
  correctedCanonicalFinalTrace_eval_S A hn nodes hnodes b chalVal pubVal orbit i

theorem honestS_zero : honestS R 0 = 0 := by
  simp [honestS]

theorem activeRequestRecords_length_eq_recordCount (pub : ComputeTable.Pub K) :
    (NockVM.activeRequestRecords pub).length = recordCount pub.state := by
  cases h : pub.state <;> simp [NockVM.activeRequestRecords, h, recordCount]

/-- **`S(i + 1) = S(i) + arity(state i)`** for the honest fill. -/
theorem honestS_step (i : Fin R.problem.cfg.compRows) :
    honestS R ((i : ℕ) + 1) =
      honestS R i + recordCount (R.problem.exec.computePubAt i).state := by
  rw [OptimizedComputeCanonicalSatisfaction.honestS_succ,
    activeRequestRecords_length_eq_recordCount]

/-- **The honest exponent of the `j`-th active request of row `i` is `S(i) + j + 1`**, its
`1`-based position in the derived request list. -/
theorem honest_request_exponent (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.compRows) (j : ℕ)
    (hj : j < (NockVM.activeRequestRecords (R.problem.exec.computePubAt i)).length) :
    RecordCarrier.honestExp R.problem.exec.derivedRequestIO
        (NockVM.encRecFormR ((NockVM.activeRequestRecords (R.problem.exec.computePubAt i))[j])
          R.problem.cfg.challenges.lam) =
      honestS R i + j + 1 :=
  honestExp_activeRequest A i j hj

/-! ## B. Memory `reqIdx` -/

/-- **The canonical carrier column is the honest fill.** -/
theorem canonical_reqIdx (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (kMem : ℕ) (i : Fin R.problem.cfg.memRows) :
    (canonicalSourceTrace A nodes b kMem ⟨181, by omega⟩).eval (nodes i) = honestReqIdx R i :=
  canonicalSourceTrace_reqIdx A nodes hnodes b kMem i

/-- `0` on every row that touches no live memory record. -/
theorem honest_reqIdx_inactive (i : Fin R.problem.cfg.memRows)
    (h1 : (R.problem.exec.memoryPubAt i).st ≠ .read_root)
    (h2 : (R.problem.exec.memoryPubAt i).st ≠ .verify_child) :
    honestReqIdx R i = 0 := by
  simp [honestReqIdx, reqIdxNat, h1, h2]

/-- **On a `read_root` / `verify_child` row the fill is the exponent of the request the row's
record answers**: if the row's encoded record is the `j`-th active request of compute row `i'`,
then `reqIdx = S(i') + j + 1`. -/
theorem honest_reqIdx_eq_request_exponent (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows)
    (hst : (R.problem.exec.memoryPubAt i).st = .read_root ∨
      (R.problem.exec.memoryPubAt i).st = .verify_child)
    (i' : Fin R.problem.cfg.compRows) (j : ℕ)
    (hj : j < (NockVM.activeRequestRecords (R.problem.exec.computePubAt i')).length)
    (hrec : NockVM.encRecC (R.problem.exec.memoryPubAt i).mem
        (R.problem.exec.memoryPubAt i).cprime =
      NockVM.encRecFormR ((NockVM.activeRequestRecords (R.problem.exec.computePubAt i'))[j])
        R.problem.cfg.challenges.lam) :
    honestReqIdx R i = ((honestS R i' + j + 1 : ℕ) : F) := by
  simp only [honestReqIdx, reqIdxNat, if_pos hst, hrec]
  rw [honest_request_exponent A i' j hj]

/-- **Duplicate lookups are included**: two live rows serving the same record carry the same
`reqIdx` (the fill is a function of the record). -/
theorem honest_reqIdx_duplicate (i i' : Fin R.problem.cfg.memRows)
    (hst : (R.problem.exec.memoryPubAt i).st = .read_root ∨
      (R.problem.exec.memoryPubAt i).st = .verify_child)
    (hst' : (R.problem.exec.memoryPubAt i').st = .read_root ∨
      (R.problem.exec.memoryPubAt i').st = .verify_child)
    (hrec : NockVM.encRecC (R.problem.exec.memoryPubAt i).mem
        (R.problem.exec.memoryPubAt i).cprime =
      NockVM.encRecC (R.problem.exec.memoryPubAt i').mem
        (R.problem.exec.memoryPubAt i').cprime) :
    honestReqIdx R i = honestReqIdx R i' := by
  simp only [honestReqIdx, reqIdxNat, if_pos hst, if_pos hst', hrec]

end

/-! ## C. The α-free template: `recordExponent` is the prefix sum (pre-`α`) -/

section Template

open SemanticTimestampStrategy

/-- Along a line-exponent chain, the line exponent of row `k` is the head's plus the prefix sum of
`recordCount`. -/
theorem lnPrev_prefix_of_chain :
    ∀ (L : List ComputeTimestampRow), ComputeLineExponentChain L →
      (∀ s ∈ L, s.lnExponent = s.lnPrevExponent + recordCount s.state) →
      ∀ (k : ℕ) (hk : k < L.length) (h0 : 0 < L.length),
        (L[k]'hk).lnPrevExponent =
          (L[0]'h0).lnPrevExponent + ((L.take k).map fun s => recordCount s.state).sum
  | [], _, _, k, hk, _ => absurd hk (by simp)
  | [a], _, _, k, hk, _ => by
      have : k = 0 := by simpa using hk
      subst this; simp
  | a :: b :: rest, hchain, hadv, k, hk, h0 => by
      cases k with
      | zero => simp
      | succ k =>
          have hk' : k < (b :: rest).length := by simpa using hk
          have ih := lnPrev_prefix_of_chain (b :: rest) hchain.2
            (fun s hs => hadv s (List.mem_cons_of_mem _ hs)) k hk' (by simp)
          have hab : a.lnExponent = b.lnPrevExponent := hchain.1
          have ha := hadv a (by simp)
          simp only [List.getElem_cons_succ, List.getElem_cons_zero] at ih ⊢
          rw [ih, ← hab, ha]
          simp [List.take_succ_cons, List.map_cons, List.sum_cons]
          ring

theorem startsAtZero_head :
    ∀ (L : List ComputeTimestampRow) (h0 : 0 < L.length), ComputeLineStartsAtZero L →
      (L[0]'h0).lnPrevExponent = 0
  | [], h0, _ => absurd h0 (by simp)
  | _ :: _, _, hs => hs

/-- **The template's line exponent is the prefix sum** (`S = prefixExp`, α-free): row `k` of
any `SemanticTimestampSkeleton` has `lnPrevExponent = Σ_{k' < k} recordCount(state k')`. -/
theorem template_lnPrev_eq_prefix {F K : Type} [Field F] [Field K] [Algebra F K]
    {base : SemanticStrategy.SemanticSkeleton}
    (T : SemanticTimestampSkeleton F K base) (k : ℕ) (hk : k < T.computeRows.length) :
    (T.computeRows[k]'hk).lnPrevExponent =
      ((T.computeRows.take k).map fun s => recordCount s.state).sum := by
  have h0 : 0 < T.computeRows.length := by omega
  rw [lnPrev_prefix_of_chain T.computeRows T.computeLineChain T.computeLineAdvance k hk h0]
  have hz : (T.computeRows[0]'h0).lnPrevExponent = 0 :=
    startsAtZero_head T.computeRows h0 T.computeStartsAtZero
  rw [hz, zero_add]

/-- **The template's `recordExponent` is `prefix + i + 1`** — the honest fill's `S(i) + j + 1`. -/
theorem template_recordExponent_eq_prefix {F K : Type} [Field F] [Field K] [Algebra F K]
    {base : SemanticStrategy.SemanticSkeleton}
    (T : SemanticTimestampSkeleton F K base) (k : ℕ) (hk : k < T.computeRows.length)
    (i : Fin 3) (hi : (i : ℕ) < recordCount (T.computeRows[k]'hk).state) :
    (T.computeRows[k]'hk).recordExponent i =
      ((T.computeRows.take k).map fun s => recordCount s.state).sum + (i : ℕ) + 1 := by
  rw [T.computeRecordOffsets _ (List.getElem_mem hk) i hi, template_lnPrev_eq_prefix T k hk]

end Template

end Nock.RedTeam.Batch671

#print axioms Nock.RedTeam.Batch671.canonical_S
#print axioms Nock.RedTeam.Batch671.honestS_step
#print axioms Nock.RedTeam.Batch671.honest_request_exponent
#print axioms Nock.RedTeam.Batch671.canonical_reqIdx
#print axioms Nock.RedTeam.Batch671.honest_reqIdx_eq_request_exponent
#print axioms Nock.RedTeam.Batch671.honest_reqIdx_duplicate
#print axioms Nock.RedTeam.Batch671.template_lnPrev_eq_prefix
#print axioms Nock.RedTeam.Batch671.template_recordExponent_eq_prefix
