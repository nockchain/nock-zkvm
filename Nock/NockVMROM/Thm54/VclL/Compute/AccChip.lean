import Nock.NockVMROM.Thm54.VclL.Compute.AccVCL
import Nock.NockVMROM.Thm54.VclL.Compute.RowDecode

/-!
# V4T step 1c : accepted traces of `computeChipVCLE` are accepted row families

.  `acceptedRows_of_sat`: from
acceptance at `computeChipVCLE`, injective nodes, row adjacency `nodes (i+1) = ω · nodes i` and the
characteristic hypothesis `hchar` (as at the deployed chip), the row envs form an
`AcceptedRows` family — so `exportReqFacts` / `pathReqFacts`  are the chip's
`reqFacts`, with no trace premise.  `selAt_of_gates`: the one-hot state in `𝔽` from the base gates.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock Nock.Reified Nock.Framework Nock.Framework.Reify Module
open Nock.ComputeTable (State)
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.ComputePaperPacking
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem selIdx_opCol (t : State) : Nock.Reified.opCol t = selIdx t := by cases t <;> rfl

theorem exists_selIdx (i : ℕ) (hi : i < 11) : ∃ t : State, selIdx t = i := by
  interval_cases i
  exacts [⟨.s0, rfl⟩, ⟨.s1, rfl⟩, ⟨.s2, rfl⟩, ⟨.s3, rfl⟩, ⟨.s4, rfl⟩, ⟨.s5, rfl⟩, ⟨.s6, rfl⟩,
    ⟨.s7, rfl⟩, ⟨.s8, rfl⟩, ⟨.s9, rfl⟩, ⟨.cons, rfl⟩]

theorem selIdx_inj {t t' : State} (h : selIdx t = selIdx t') : t = t' := by
  cases t <;> cases t' <;> simp_all [selIdx]

/-- **The one-hot state in `𝔽` from the gates** of `computeChipVCLE` at a row. -/
theorem selAt_of_gates [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) (env : Env F)
    (hg : ∀ g ∈ vclGatesE n b γc ρc, g.eval env = 0)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1) : ∃ st, SelAt env st := by
  have hv : ∀ g ∈ vclGates n b, g.eval env = 0 := fun g hm => hg g (by
    simp only [vclGatesE, vclGatesD, vclGatesA, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hm))))
  have hs := VclSourceObligations.of_vclGates n b env hv
  obtain ⟨st, hone⟩ := oneHot_of_base15 n b _ hs.base15 hchar
  refine ⟨st, fun i hi => ?_⟩
  obtain ⟨t, rfl⟩ := exists_selIdx i hi
  have h1 := hone t
  rw [selIdx_opCol, source_trace_base _ _ (by cases t <;> decide)] at h1
  have h2 : (pullEnv env).trace (selIdx t) = env.trace (selIdx t) :=
    pullEnv_trace_lt _ _ (by cases t <;> decide)
  change algebraMap F K ((pullEnv env).trace (selIdx t)) = _ at h1
  rw [h2] at h1
  have hF : env.trace (selIdx t) = if t = st then 1 else 0 := by
    by_cases ht : t = st
    · rw [if_pos ht] at h1 ⊢
      exact (algebraMap F K).injective (by rw [h1, map_one])
    · rw [if_neg ht] at h1 ⊢
      exact (algebraMap F K).injective (by rw [h1, map_zero])
  cases st <;> cases t <;> simpa [selIdx] using hF

/-- The row envs of a trace at the nodes (`0` beyond `N`). -/
def rowEnvs {h n w : ℕ} (nodes : Fin n → F) (ω : F) (P : Fin w → F[X]) (chalV pubVal : ℕ → F) :
    ℕ → Env F :=
  fun i => if hi : i < n then envOfTrace P ω (nodes ⟨i, hi⟩) chalV pubVal
    else envOfTrace P ω 0 chalV pubVal

/-- **Acceptance gives an accepted row family**, hence the chip's `reqFacts`. -/
theorem acceptedRows_of_sat [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (γc ρc : ℕ)
    (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin 232 → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (computeChipVCLE hn nodes b γc ρc chalV pubVal orbit) P)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1) :
    AcceptedRows b γc ρc n n (rowEnvs (h := h) nodes orbit.ω P chalV pubVal) chalV pubVal := by
  have hs := (computeChipVCLE_sat_iff hn nodes b γc ρc chalV pubVal orbit P).1 hP
  have hmem : ∀ i (hi : i < n), nodes ⟨i, hi⟩ ∈ rowNodeSet nodes := fun i hi => by simp [rowNodeSet]
  have henv : ∀ i (hi : i < n), rowEnvs (h := h) nodes orbit.ω P chalV pubVal i =
      envOfTrace P orbit.ω (nodes ⟨i, hi⟩) chalV pubVal := fun i hi => by simp [rowEnvs, hi]
  have hgates : ∀ i < n, ∀ g ∈ vclGatesE n b γc ρc,
      g.eval (rowEnvs (h := h) nodes orbit.ω P chalV pubVal i) = 0 := by
    intro i hi g hg
    rw [henv i hi]; exact hs.2 _ (hmem i hi) g hg
  have h11 : (11 : ℕ) < 232 := by norm_num
  have h12 : (12 : ℕ) < 232 := by norm_num
  have m0 : P ⟨11, h11⟩ = firstRowMask nodes := hs.1 ⟨0, by change 0 < 2; norm_num⟩
  have m1 : P ⟨12, h12⟩ = lastRowMask hn nodes := hs.1 ⟨1, by change 1 < 2; norm_num⟩
  have htr11 : ∀ i (hi : i < n), (rowEnvs (h := h) nodes orbit.ω P chalV pubVal i).trace 11 =
      if i = 0 then 1 else 0 := by
    intro i hi
    rw [henv i hi]
    simp only [envOfTrace, dif_pos h11]
    rw [m0, Nock.Framework.firstRowMask_eval _ hinj]
  have htr12 : ∀ i (hi : i < n), (rowEnvs (h := h) nodes orbit.ω P chalV pubVal i).trace 12 =
      if i = n - 1 then 1 else 0 := by
    intro i hi
    rw [henv i hi]
    simp only [envOfTrace, dif_pos h12]
    rw [m1, Nock.Framework.lastRowMask_eval _ _ hinj]
    simp only [Fin.ext_iff]
  refine ⟨hn, hgates, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi j
    rw [henv i (by omega), henv (i + 1) hi]
    have ha := hadj ⟨i, by omega⟩ hi
    simp only [envOfTrace]
    split_ifs with hj
    · rw [ha]
    · rfl
  · rw [htr11 0 hn, if_pos rfl]
  · intro i hi
    rw [htr12 i (by omega), if_neg (by omega)]
  · rw [htr12 (n - 1) (by omega), if_pos rfl]
  · intro i hi
    exact selAt_of_gates n b γc ρc _ (hgates i hi) hchar
  · intro i; simp only [rowEnvs]; split_ifs <;> rfl
  · intro i; simp only [rowEnvs]; split_ifs <;> rfl

end

end VclL.Compute
end Nock.NockVMROM.Thm54
