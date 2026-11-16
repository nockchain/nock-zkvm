import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.NockVMROM.Thm54.HostileRecordLists
import Nock.NockVMROM.Thm54.GoldilocksParameters

/-!
This file is the draft's three scratch files (`FamIOFibred`,
`FamIOReadSet`, `FamIOFigures`) compiled against the QD build, under one batch name, so the
figures the §5 text quotes are receipts at the base the move will be cut from.

Three parts:

* **A. `famIO_term_eq_package_term` is `rfl`: this is byte-for-byte the IO term
  of `optimizedTrimmedProductionFailureCardBound` at QD, so REPLACING the package-chip IO lift by
  the family event moves no figure.
* **B. The read set.**  `no_slot_reads_io`: none of the thirty compute request-record slot
  expressions (after `finalSampledNamespace`) reads challenge `7` or `8` (= the IO pair `c.2.1`,
  `sampledChallengeBase = 7`).  Positive controls: the timestamp slot reads `0` (α), the Form R
  `C_slot` reads λ (`9` / `100+d`), and the sampled denominator DOES read the shifted IO γ.
* **C. The figures at QD.**  Doubled numerator `457S²+404S+28` (QD,
  `RealProgramSoundness.two_hostileTotalWork_le_of_size_formR`) gives 122 / 120 with the IO
  summand REPLACED; ADDING the family event beside the package lift gives `745S²+420S+28`, which
  is 121 / 119.  (C1) of the draft is therefore load-bearing at QD exactly as it was at PX.

No production file is touched.
-/

set_option autoImplicit false

namespace Nock.RedTeam.Batch881

/-! ## A. The fibred event (abstract) -/

section Fibred

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting

variable {K F : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype F] [DecidableEq F]

/-- The nine non-IO coordinates: `JointCoins` (αc, γ_walk, αM, z), `(a, b, c)`, `(interPole, λ)`. -/
abbrev Rest (K : Type) := JointCoins K × (FinalComputeChallengeTuple K × MemoryChallengeTuple K)

def restOf (c : OptimizedProductionChallengeTuple K F) : Rest K := (c.1, c.2.2)

instance instFintypeRest : Fintype (Rest K) :=
  inferInstanceAs (Fintype (JointCoins K × (FinalComputeChallengeTuple K × MemoryChallengeTuple K)))

instance instDecidableEqRest : DecidableEq (Rest K) :=
  inferInstanceAs (DecidableEq (JointCoins K × (FinalComputeChallengeTuple K × MemoryChallengeTuple K)))

omit [Field K] [DecidableEq K] in
theorem card_Rest : Fintype.card (Rest K) = Fintype.card K ^ 9 := by
  simp only [Rest, JointCoins, Fintype.card_prod, card_finalComputeChallengeTuple,
    card_memoryChallengeTuple]
  ring

/-- **`E_famIO` in the abstract**: records fibred over the non-IO coordinates. -/
noncomputable def famIOEvent {m : ℕ} (R : Rest K → PreChallengeRecords K m) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.filter (fun c => c.2.1 ∈ IOFailureEvent (R (restOf c)))

omit [DecidableEq F] in
theorem mem_famIOEvent {m : ℕ} (R : Rest K → PreChallengeRecords K m)
    (c : OptimizedProductionChallengeTuple K F) :
    c ∈ famIOEvent (F := F) R ↔ c.2.1 ∈ IOFailureEvent (R (restOf c)) := by
  simp [famIOEvent]

omit [DecidableEq F] in
/-- Each `(c.1, c.2.2)`-fibre injects into `IOFailureEvent (R r)` through `c ↦ c.2.1`. -/
theorem fibre_card_le {m : ℕ} (R : Rest K → PreChallengeRecords K m) (r : Rest K) :
    ((famIOEvent (F := F) R).filter (fun c => restOf c = r)).card ≤
      (IOFailureEvent (R r)).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun c : OptimizedProductionChallengeTuple K F => c.2.1) ?_ ?_
  · intro c hc
    simp only [Finset.coe_filter, famIOEvent, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hc
    obtain ⟨hmem, hr⟩ := hc
    rw [hr] at hmem
    exact hmem
  · intro c hc c' hc' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hc hc'
    have hr : restOf c = restOf c' := hc.2.trans hc'.2.symm
    have h1 : c.1 = c'.1 := congrArg (fun r : Rest K => r.1) hr
    have h2 : c.2.2 = c'.2.2 := congrArg (fun r : Rest K => r.2) hr
    have h3 : c.2.1 = c'.2.1 := h
    exact Prod.ext h1 (Prod.ext h3 h2)

theorem famIOEvent_card_le {m : ℕ} (R : Rest K → PreChallengeRecords K m) (k₁ k₂ : ℕ)
    (h1 : ∀ r, (R r).requests.length ≤ k₁) (h2 : ∀ r, (R r).responses.length ≤ k₂) :
    (famIOEvent (F := F) R).card ≤
      Fintype.card K ^ 9 * ioFailureUnionBound m k₁ k₂ (Fintype.card K) := by
  classical
  calc (famIOEvent (F := F) R).card
      = ∑ r ∈ (Finset.univ : Finset (Rest K)),
          ((famIOEvent (F := F) R).filter (fun c => restOf c = r)).card :=
        Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _r ∈ (Finset.univ : Finset (Rest K)),
          ioFailureUnionBound m k₁ k₂ (Fintype.card K) := by
        refine Finset.sum_le_sum fun r _ => ?_
        exact (fibre_card_le R r).trans
          ((IOFailureEvent_card_le (R r)).trans
            (ioFailureUnionBound_mono₂ m _ _ k₁ k₂ (Fintype.card K) (h1 r) (h2 r)))
    _ = Fintype.card K ^ 9 * ioFailureUnionBound m k₁ k₂ (Fintype.card K) := by
        rw [Finset.sum_const, Finset.card_univ, card_Rest, smul_eq_mul]

/-- **Same number as the package-chip lift** (the IO term of
`optimizedTrimmedProductionFailureCardBound` at QD, `rfl`). -/
theorem famIO_term_eq_package_term (cardK cardF p8Work N M : ℕ) :
    optimizedTrimmedProductionFailureCardBound cardK cardF p8Work
        (ioFailureUnionBound 10 (3 * N) M cardK) N M =
      p8Work * cardK ^ 3 * cardK ^ 7 + cardK ^ 9 * ioFailureUnionBound 10 (3 * N) M cardK := rfl

omit [DecidableEq F] in
/-- Positive control: a non-empty fibre makes the event non-empty. -/
theorem famIOEvent_nonempty_of {m : ℕ} (R : Rest K → PreChallengeRecords K m) (r : Rest K)
    (h : (IOFailureEvent (R r)).Nonempty) : (famIOEvent (F := F) R).Nonempty := by
  obtain ⟨q, hq⟩ := h
  refine ⟨(r.1, (q, r.2)), ?_⟩
  rw [mem_famIOEvent]
  simpa [restOf] using hq

end Fibred

/-! ## B. The read set of the thirty request-record slot expressions -/

section ReadSet

set_option maxRecDepth 4000

open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution

/-- Challenge indices read by an `Expr`. -/
def chalIdx : Expr → List ℕ
  | .Var .challenge i => [i]
  | .Var _ _ => []
  | .Const _ => []
  | .Add a b => chalIdx a ++ chalIdx b
  | .Sub a b => chalIdx a ++ chalIdx b
  | .Mul a b => chalIdx a ++ chalIdx b
  | .Neg a => chalIdx a
  | .Pow a _ => chalIdx a

/-- The slot expression `HostileRecordLists.rowRecord` evaluates (its case split, verbatim). -/
def slotExpr (j : Fin 3) (c : Fin 10) : Expr :=
  if (c : ℕ) = 9 then (sampledSlotE .traceCur (67 + 8 * (j : ℕ))).subst finalSampledNamespace
  else if (c : ℕ) = 6 then (sampledSlotT .traceCur (67 + 8 * (j : ℕ))).subst finalSampledNamespace
  else if (c : ℕ) = 8 then (sampledSlotC .traceCur (67 + 8 * (j : ℕ))).subst finalSampledNamespace
  else (computeTraceSubst .traceCur (67 + 8 * (j : ℕ) + (c : ℕ))).subst finalSampledNamespace

theorem sampledChallengeBase_eq : sampledChallengeBase = 7 := rfl

/-- **No request-record slot reads the IO pair** (production slots `7`/`8` = `(γ, pole)` =
`c.2.1`). -/
theorem no_slot_reads_io :
    ∀ j : Fin 3, ∀ c : Fin 10, ∀ i ∈ chalIdx (slotExpr j c), i ≠ 7 ∧ i ≠ 8 := by
  decide +kernel

/-- Positive control: the timestamp slot reads challenge `0` (α). -/
theorem ts_slot_reads_alpha : 0 ∈ chalIdx (slotExpr 0 7) := by decide +kernel

/-- Positive control: the Form R `C_slot` reads λ (slot `9` or a λ-power `100 + d`). -/
theorem cslot_reads_lambda : ∃ i ∈ chalIdx (slotExpr 0 8), i = 9 ∨ 100 ≤ i := by decide +kernel

/-- Second positive control: the sampled denominator DOES read the shifted IO γ. -/
theorem denominator_reads_io :
    sampledChallengeBase ∈ chalIdx ((sampledRecordRLC .traceCur 67).subst finalSampledNamespace) := by
  decide +kernel

end ReadSet

/-! ## C. The figures at QD -/

section Figures

open Nock.NockVMROM.Thm54.GoldilocksParameters

/-- `Crit c l k r b`: doubled numerator `c·S² + l·S + k` at `S = 2^r` gives `b` bits. -/
def Crit (c l k r b : ℕ) : Prop := (c * (2 ^ r * 2 ^ r) + l * 2 ^ r + k) * 2 ^ b < 2 * cardKGold

theorem replaced_457_122 : Crit 457 404 28 31 122 := by unfold Crit; norm_num
theorem replaced_457_120 : Crit 457 404 28 32 120 := by unfold Crit; norm_num
theorem replaced_463_122 : Crit 463 402 28 31 122 := by unfold Crit; norm_num
theorem replaced_463_120 : Crit 463 402 28 32 120 := by unfold Crit; norm_num

/-- The IO summand's doubled share at `N = M = S`: `2·(9(3S+S)² + 2(3S+S)) = 288S² + 16S`. -/
theorem io_share (S : ℕ) :
    2 * (9 * ((3 * S + S) * (3 * S + S)) + 2 * (3 * S + S)) = 288 * (S * S) + 16 * S := by
  ring

/-- ADDED beside the package-chip lift: `457 + 288 = 745`, `404 + 16 = 420` — 122 is LOST. -/
theorem doubled_745_not_122 : ¬ Crit 745 420 28 31 122 := by unfold Crit; norm_num
theorem doubled_745_121 : Crit 745 420 28 31 121 := by unfold Crit; norm_num
theorem doubled_745_not_120_at_32 : ¬ Crit 745 420 28 32 120 := by unfold Crit; norm_num
theorem doubled_745_119_at_32 : Crit 745 420 28 32 119 := by unfold Crit; norm_num
theorem doubled_751_not_122 : ¬ Crit 751 418 28 31 122 := by unfold Crit; norm_num

/-- The `S²` ceiling at `r = 31` / 122 bits is 511; 745 is far past it. -/
theorem ceiling_31 : Crit 511 420 28 31 122 ∧ ¬ Crit 512 0 0 31 122 := by
  constructor <;> (unfold Crit; norm_num)

end Figures

end Nock.RedTeam.Batch881

#print axioms Nock.RedTeam.Batch881.famIOEvent_card_le
#print axioms Nock.RedTeam.Batch881.famIO_term_eq_package_term
#print axioms Nock.RedTeam.Batch881.no_slot_reads_io
#print axioms Nock.RedTeam.Batch881.denominator_reads_io
#print axioms Nock.RedTeam.Batch881.replaced_457_122
#print axioms Nock.RedTeam.Batch881.doubled_745_not_122
