/-
  Nock/NockVMROM/Thm54/BelowDefs/Unhosted309Events.lean

  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/Unhosted309Events.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs` or the statement file, directly or transitively.
-/
import Nock.NockVMROM.Thm54.P8Core.RepartitionedStaging
import Nock.NockVMROM.Thm54.Unhosted309Realization

namespace Nock.NockVMROM.Thm54

namespace Unhosted309

open Nock
open Nock.Reified
open Nock.Framework Reify
open Nock.ComputeTable
open Nock.Walk
open OptimizedComputeSubstitution
open OptimizedComputeCorrectedFinal
open OptimizedStrictPackage
open ComputeWalkRootEvents
open ComputeWalkLabel
open RepartitionedStaging
open RoundFibred
open scoped Polynomial
set_option linter.unusedSectionVars false

noncomputable section

/-- A source index of the 309 decode whose physical columns are committed in `B0 ∪ B1`. -/
def goodSrc : VarKind × ℕ → Bool
  | (.traceCur, j) => decide (j < 13 ∨ (13 ≤ j ∧ j < 76 ∧ j - 13 < 58 ∧ ¬ (32 ≤ j - 13 ∧ j - 13 ≤ 35)))
  | _ => false

def allStatesL : List State := [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .cons]

/-- **Receipt: the restored fingerprint sources and the hosted child tags read only `B0 ∪ B1`.** -/
theorem decoder_reads_B01 :
    (∀ role, role < 12 → ∀ coord, coord < 3 →
        ∀ q ∈ readsE (semanticPub .traceCur role coord), goodSrc q = true) ∧
      (∀ st ∈ allStatesL, ∀ j : Fin 3, ∀ q ∈ readsE (childTagHost curReader st j), goodSrc q = true) := by
  decide

section Decoders

variable {K : Type} [Field K]

theorem allStatesL_mem (st : State) : st ∈ allStatesL := by cases st <;> decide

theorem ofSubst_trace_congr_good {E E' : Env K}
    (h : ∀ q, goodSrc q = true → varVal E q.1 q.2 = varVal E' q.1 q.2) (k : ℕ)
    (hk : 11 ≤ k ∧ k < 47) :
    (Env.ofSubst computeSubst E).trace k = (Env.ofSubst computeSubst E').trace k := by
  have h11 : ¬ k < 11 := by omega
  have h47 : k < 47 := hk.2
  simp only [Env.ofSubst, computeSubst, computeTraceSubst, h11, h47, if_false, if_true]
  apply eval_congr_reads
  intro q hq
  exact h q (decoder_reads_B01.1 _ (by omega) _ (Nat.mod_lt _ (by norm_num)) q hq)

theorem fpOf_congr_good {E E' : Env K}
    (h : ∀ q, goodSrc q = true → varVal E q.1 q.2 = varVal E' q.1 q.2) (b : ℕ)
    (hb : 11 ≤ b ∧ b + 2 < 47) :
    Nock.Reified.fpOf (Env.ofSubst computeSubst E) b =
      Nock.Reified.fpOf (Env.ofSubst computeSubst E') b := by
  simp only [Nock.Reified.fpOf]
  rw [ofSubst_trace_congr_good h b (by omega), ofSubst_trace_congr_good h (b + 1) (by omega),
    ofSubst_trace_congr_good h (b + 2) (by omega)]

theorem rowStateOf_congr_good {E E' : Env K}
    (h : ∀ q, goodSrc q = true → varVal E q.1 q.2 = varVal E' q.1 q.2) :
    rowStateOf E = rowStateOf E' := by
  have ht : ∀ j, 1 ≤ j → j ≤ 10 → E.trace j = E'.trace j := fun j h1 h2 =>
    h (.traceCur, j) (by simp [goodSrc]; omega)
  unfold rowStateOf
  rw [ht 1 (by omega) (by omega), ht 2 (by omega) (by omega), ht 3 (by omega) (by omega),
    ht 4 (by omega) (by omega), ht 5 (by omega) (by omega), ht 6 (by omega) (by omega),
    ht 7 (by omega) (by omega), ht 8 (by omega) (by omega), ht 9 (by omega) (by omega),
    ht 10 (by omega) (by omega)]

/-- **The decoded label, child payloads and fanout are functions of the `B0 ∪ B1` reads.** -/
theorem decoders_congr_good {E E' : Env K}
    (h : ∀ q, goodSrc q = true → varVal E q.1 q.2 = varVal E' q.1 q.2) :
    rowLabelVec E = rowLabelVec E' ∧ (∀ l, rowChildVec E l = rowChildVec E' l) ∧
      rowFanout E = rowFanout E' := by
  have hst := rowStateOf_congr_good h
  have hfp := fpOf_congr_good h
  have hpub : ∀ b, 11 ≤ b → b + 2 < 47 →
      Nock.Reified.fpOf (Env.ofSubst computeSubst E) b =
        Nock.Reified.fpOf (Env.ofSubst computeSubst E') b := fun b h1 h2 => hfp b ⟨h1, h2⟩
  refine ⟨?_, ?_, ?_⟩
  · funext k
    fin_cases k <;>
      simp only [rowLabelVec, rowPub, Nock.Reified.pubOfState, labelVecOfPub, hst,
        hpub 11 (by omega) (by omega), hpub 14 (by omega) (by omega),
        hpub 17 (by omega) (by omega)]
  · have htags : rowTags E = rowTags E' := by
      funext j
      simp only [rowTags, hst]
      apply eval_congr_reads
      intro q hq
      exact h q (decoder_reads_B01.2 _ (allStatesL_mem _) j q hq)
    have hsf : ∀ j, sfTriple (rowPub E) j = sfTriple (rowPub E') j := by
      intro j
      fin_cases j <;>
        simp only [sfTriple, rowPub, Nock.Reified.pubOfState,
          hpub 20 (by omega) (by omega), hpub 23 (by omega) (by omega),
          hpub 26 (by omega) (by omega), hpub 29 (by omega) (by omega),
          hpub 32 (by omega) (by omega), hpub 35 (by omega) (by omega),
          hpub 38 (by omega) (by omega), hpub 41 (by omega) (by omega),
          hpub 44 (by omega) (by omega)]
    intro l
    unfold rowChildVec
    match l with
    | 0 => funext k; fin_cases k <;> simp only [childVecN, childVec, htags, hsf 0]
    | 1 => funext k; fin_cases k <;> simp only [childVecN, childVec, htags, hsf 1]
    | 2 => funext k; fin_cases k <;> simp only [childVecN, childVec, htags, hsf 2]
    | n + 3 => rfl
  · simp only [rowFanout, hst]

end Decoders

section Package

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] {hOrb : ℕ}

theorem physOf_good_round (j c : ℕ) (hj : goodSrc (.traceCur, j) = true) (hc : physOf j c) :
    c < 309 ∧ newComputeColRound c ≤ 1 := by
  simp only [goodSrc, decide_eq_true_eq] at hj
  unfold physOf at hc
  refine ⟨by omega, ?_⟩
  unfold newComputeColRound newComputeRoleRound
  have hr : (c - 13) / 3 = j - 13 ∨ c < 13 := by omega
  split_ifs <;> simp_all <;> omega

end Package

end

end Unhosted309

end Nock.NockVMROM.Thm54
