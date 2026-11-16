/-
  Nock/RedTeam/Batch917Thm54Part2bNestedDischarge.lean

  Nothing consumes this.

  `r4_path_valid_at` (QC, `Batch824`) concludes, for every decoded root `t`, (i) `∀ e, readCount e t =
  verifyCount e t` and (ii) `∀ e, Paired e t → ∃ q, rpaths e t = [q] ∧ vpaths e t = [q ++ bitsOf m c]`.
  With `UniqueExponents t` (PY, `uniqueExponents_decoded_at`) and `bitsOf m c ≠ []` (shift ≥ 1, i.e. the
  record's Nock axis is ≥ 2), this gives `AxisBridge.ReadVerifyNested t`: every read's verify sits STRICTLY
  below it.  So the checker conjunct `readVerifyNestedCheck` of `ProductionStrategy.Accepts` can be DERIVED on
  decoded trees — no checker edit, no `Accepts` firing, no rewrite of its 16 capstone consumers.
  Paths record only `decompose` branches, so a unary chain `.verify e _ (.read e c)` puts both nodes at the
  same path; the STRICT prefix `q ≠ v` excludes the verify-above-read placement.
-/
import Nock.NockVMROM.Thm54.FormRCore.PwFunctional
import Nock.NockVMROM.Thm54.FormRCore.Mtree
import Nock.AxisBridge

namespace Nock.RedTeam.Batch917

open Nock Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.RedTeam.Batch554 Nock.RedTeam.Batch575


variable {K : Type} [Field K]

/-- `|rpaths e t| = readCount e t`. -/
theorem rpaths_length (e : ℕ) : ∀ t : MTree K, (rpaths e t).length = readCount e t
  | .halt => by simp [rpaths, readCount]
  | .decompose l r => by
      simp [rpaths, readCount, rpaths_length e l, rpaths_length e r]
  | .read e' c => by
      by_cases h : e' = e <;> simp [rpaths, readCount, h, rpaths_length e c] <;> omega
  | .verify e' a c => by simp [rpaths, readCount, rpaths_length e c]

/-- `|vpaths e t| = verifyCount e t`. -/
theorem vpaths_length (e : ℕ) : ∀ t : MTree K, (vpaths e t).length = verifyCount e t
  | .halt => by simp [vpaths, verifyCount]
  | .decompose l r => by
      simp [vpaths, verifyCount, vpaths_length e l, vpaths_length e r]
  | .read e' c => by simp [vpaths, verifyCount, vpaths_length e c]
  | .verify e' a c => by
      by_cases h : e' = e <;> simp [vpaths, verifyCount, h, vpaths_length e c] <;> omega

/-- The path characterization: every read of `e` at path `q` has a verify of `e` at a path
STRICTLY extending `q`. -/
def StrictBelow (t : MTree K) : Prop :=
  ∀ e q, q ∈ rpaths e t → ∃ v ∈ vpaths e t, q <+: v ∧ q ≠ v

theorem readVerifyNested_of_strictBelow : ∀ t : MTree K, StrictBelow t → ReadVerifyNested t
  | .halt, _ => trivial
  | .decompose l r, h => by
      refine ⟨readVerifyNested_of_strictBelow l ?_, readVerifyNested_of_strictBelow r ?_⟩
      · intro e q hq
        have hq' : (false :: q) ∈ rpaths e (.decompose l r) := by
          simp only [rpaths, List.mem_append, List.mem_map]; exact Or.inl ⟨q, hq, rfl⟩
        obtain ⟨v, hv, hpre, hne⟩ := h e _ hq'
        simp only [vpaths, List.mem_append, List.mem_map] at hv
        rcases hv with ⟨v', hv', rfl⟩ | ⟨v', hv', rfl⟩
        · refine ⟨v', hv', ?_, ?_⟩
          · exact (List.cons_prefix_cons.mp hpre).2
          · intro h'; exact hne (by rw [h'])
        · exact absurd (List.cons_prefix_cons.mp hpre).1 (by decide)
      · intro e q hq
        have hq' : (true :: q) ∈ rpaths e (.decompose l r) := by
          simp only [rpaths, List.mem_append, List.mem_map]; exact Or.inr ⟨q, hq, rfl⟩
        obtain ⟨v, hv, hpre, hne⟩ := h e _ hq'
        simp only [vpaths, List.mem_append, List.mem_map] at hv
        rcases hv with ⟨v', hv', rfl⟩ | ⟨v', hv', rfl⟩
        · exact absurd (List.cons_prefix_cons.mp hpre).1 (by decide)
        · refine ⟨v', hv', ?_, ?_⟩
          · exact (List.cons_prefix_cons.mp hpre).2
          · intro h'; exact hne (by rw [h'])
  | .read e' c, h => by
      refine ⟨?_, readVerifyNested_of_strictBelow c ?_⟩
      · have hq : ([] : List Bool) ∈ rpaths e' (.read e' c) := by simp [rpaths]
        obtain ⟨v, hv, _, _⟩ := h e' [] hq
        simp only [vpaths] at hv
        have hlen := vpaths_length e' c
        have : 0 < (vpaths e' c).length := List.length_pos_of_mem hv
        omega
      · intro e q hq
        have hq' : q ∈ rpaths e (.read e' c) := by
          simp [rpaths]; exact Or.inr hq
        obtain ⟨v, hv, hpre, hne⟩ := h e q hq'
        exact ⟨v, by simpa [vpaths] using hv, hpre, hne⟩
  | .verify e' a c, h => by
      show ReadVerifyNested c
      refine readVerifyNested_of_strictBelow c ?_
      intro e q hq
      have hq' : q ∈ rpaths e (.verify e' a c) := by simpa [rpaths] using hq
      obtain ⟨v, hv, hpre, hne⟩ := h e q hq'
      simp only [vpaths, List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at hv
      rcases hv with ⟨_, rfl⟩ | hv
      · exact absurd (List.prefix_nil.mp hpre) hne
      · exact ⟨v, hv, hpre, hne⟩

/-- **The discharge.**  Balance (R4 (i)), unique exponents (PY) and the strict path equation
(R4 (ii) with a nonempty bit string) give `ReadVerifyNested`. -/
theorem readVerifyNested_of_formR_paths (t : MTree K)
    (hU : UniqueExponents t)
    (hbal : ∀ e, readCount e t = verifyCount e t)
    (hpath : ∀ e, Paired e t → ∃ q b, b ≠ [] ∧ rpaths e t = [q] ∧ vpaths e t = [q ++ b]) :
    ReadVerifyNested t := by
  apply readVerifyNested_of_strictBelow
  intro e q hq
  have hr1 : readCount e t = 1 := by
    have hpos : 0 < readCount e t := by
      rw [← rpaths_length]; exact List.length_pos_of_mem hq
    have := (hU e).1; omega
  have hpaired : Paired e t := ⟨hr1, by rw [← hbal]; exact hr1⟩
  obtain ⟨q', b, hb, hr, hv⟩ := hpath e hpaired
  have hqq : q = q' := by rw [hr] at hq; simpa using hq
  subst hqq
  refine ⟨q ++ b, by simp [hv], List.prefix_append _ _, ?_⟩
  intro h
  exact hb (by simpa using h.symm)

end Nock.RedTeam.Batch917

#print axioms Nock.RedTeam.Batch917.readVerifyNested_of_formR_paths
