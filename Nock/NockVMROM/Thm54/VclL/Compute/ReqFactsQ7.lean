import Nock.NockVMROM.Thm54.VclL.Compute.PatchQ7
import Nock.NockVMROM.Thm54.VclL.Compute.AccChip

/-!
# V4T3 step (c) : `reqFacts` at the Q7 chip

.

* `export_invQ7` / `path_invQ7`, `AcceptedRowsQ7`, **`exportReqFactsQ7`**, **`pathReqFactsQ7`**;
* `selAt_of_gatesQ7` (one-hot from the Q7 base gates), **`acceptedRowsQ7_of_sat`** — acceptance at
  `computeChipVCLQ7` (injective nodes, adjacency, `hchar`) gives the accepted row family.

Coin-map parametric: the IO coins are read at limb bases `γc`/`ρc` of `chalV` (`coinsV`); at
`frameVCL` (`computeChipQ7`) `γc = 21`, `ρc = 24` (`chalVQ7_io`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock Nock.Reified Nock.Framework Nock.Framework.Reify Module
open Nock.ComputeTable (State)
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.ComputePaperPacking
open scoped Polynomial

set_option maxRecDepth 300000

noncomputable section

section rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq K]

/-- Active export slots have their reciprocal: `inv · compress(rec) = 1`. -/
theorem export_invQ7 (b : Basis (Fin 3) F K) (γc ρc : ℕ) (n : ℕ) (env : Env F) (st : State)
    (h : SelAt env st) (hg : ∀ g ∈ vclGatesQ7 n b γc ρc, g.eval env = 0) (s : ℕ)
    (hs : s < 3) (ha : actX (K := K) env s = 1) :
    invVal b env (invBaseX s) * FiniteIO.compress (coinsAt b env γc ρc) (recX b env s) = 1 := by
  have hD : ∀ g ∈ lookupGatesD b γc ρc, g.eval env = 0 := fun g hm =>
    hg g (by simp only [vclGatesQ7, List.mem_append]; exact Or.inl (Or.inl (Or.inr hm)))
  have ht := selAt_trace h
  rcases s with _ | _ | _ | s
  · exact slot0_sound b γc ρc env fun g hm => hD g (by simp [lookupGatesD, hm])
  · have hx : st = .s2 ∨ st = .s5 ∨ st = .s6 ∨ st = .s7 ∨ st = .s8 ∨ st = .s9 := by
      simp only [actX, selSum_eval, slot1ExportSels, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil] at ha
      rw [ht 2 (by norm_num), ht 5 (by norm_num), ht 6 (by norm_num), ht 7 (by norm_num),
        ht 8 (by norm_num), ht 9 (by norm_num)] at ha
      cases st <;> simp [selIdx] at ha ⊢
    have hsel : SelAt env st := h
    exact slot1_sound_export b γc ρc env st hsel hx fun g hm => hD g (by simp [lookupGatesD, hm])
  · have h6 : st = .s6 := by
      simp only [actX] at ha; rw [ht 6 (by norm_num)] at ha
      cases st <;> simp [selIdx] at ha ⊢
    subst h6
    exact slot2_sound_s6 b γc ρc env h fun g hm => hD g (by simp [lookupGatesD, hm])
  · omega

theorem path_invQ7 (b : Basis (Fin 3) F K) (γc ρc : ℕ) (n : ℕ) (env : Env F) (st : State)
    (h : SelAt env st) (hg : ∀ g ∈ vclGatesQ7 n b γc ρc, g.eval env = 0) (s : ℕ)
    (hs : s < 2) (ha : actP (K := K) env s = 1) :
    invVal b env (invBaseP s) * FiniteIO.compress (coinsAt b env γc ρc) (recP b env s) = 1 := by
  have hD : ∀ g ∈ lookupGatesD b γc ρc, g.eval env = 0 := fun g hm =>
    hg g (by simp only [vclGatesQ7, List.mem_append]; exact Or.inl (Or.inl (Or.inr hm)))
  have ht := selAt_trace h
  rcases s with _ | _ | s
  · have h0 : st = .s0 := by
      simp only [actP] at ha; rw [ht 0 (by norm_num)] at ha
      cases st <;> simp [selIdx] at ha ⊢
    subst h0
    exact slot1_sound_s0 b γc ρc env h fun g hm => hD g (by simp [lookupGatesD, hm])
  · have h9 : st = .s9 := by
      simp only [actP] at ha; rw [ht 9 (by norm_num)] at ha
      cases st <;> simp [selIdx] at ha ⊢
    subst h9
    exact slot2_sound_s9 b γc ρc env h fun g hm => hD g (by simp [lookupGatesD, hm])
  · omega

end rows

section facts
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq K]

structure AcceptedRowsQ7 (b : Basis (Fin 3) F K) (γc ρc : ℕ) (n N : ℕ) (envs : ℕ → Env F)
    (chalV pubVal : ℕ → F) : Prop where
  hN : 0 < N
  gates : ∀ i < N, ∀ g ∈ vclGatesQ7 n b γc ρc, g.eval (envs i) = 0
  shift : ∀ i, i + 1 < N → ∀ j, (envs i).traceNext j = (envs (i + 1)).trace j
  first : (envs 0).trace 11 = 1
  notLast : ∀ i, i + 1 < N → (envs i).trace 12 = 0
  last : (envs (N - 1)).trace 12 = 1
  sel : ∀ i < N, ∃ st, SelAt (envs i) st
  chal : ∀ i, (envs i).chal = chalV
  pub : ∀ i, (envs i).pub = pubVal

/-- **The export accumulator's `reqFacts`**: on an accepted row family, the active export records
have reciprocal compressed denominators summing to the public `ρ_export`. -/
def exportReqFactsQ7 (b : Basis (Fin 3) F K) (γc ρc n N : ℕ) (envs : ℕ → Env F) (chalV pubVal : ℕ → F)
    (A : AcceptedRowsQ7 b γc ρc n N envs chalV pubVal) :
    ReqIOFacts (FiniteIO.compress (m := 10) (coinsV b chalV γc ρc)) (limbVal b pubVal rhoExportPub) := by
  classical
  let act : ℕ → ℕ → K := fun i s => if i < N then actX (envs i) s else 0
  let inv : ℕ → ℕ → K := fun i s => if act i s = 1 then invVal b (envs i) (invBaseX s) else 0
  have hbool : ∀ i s, act i s = 0 ∨ act i s = 1 := by
    intro i s
    by_cases hi : i < N
    · obtain ⟨st, hst⟩ := A.sel i hi
      simp only [act, hi, if_true]; exact actX_bool _ st hst s
    · left; simp [act, hi]
  have hinv : ∀ i s, s < 3 → inv i s *
      FiniteIO.compress (coinsV b chalV γc ρc) (recX b (envs i) s) = act i s := by
    intro i s hs
    by_cases ha : act i s = 1
    · have hi : i < N := by by_contra hi; simp [act, hi] at ha
      obtain ⟨st, hst⟩ := A.sel i hi
      have ha' : actX (K := K) (envs i) s = 1 := by simpa [act, hi] using ha
      simp only [inv, ha, if_true]
      rw [← coinsAt_eq b γc ρc (envs i) chalV (A.chal i)]
      exact export_invQ7 b γc ρc n (envs i) st hst (A.gates i hi) s hs ha'
    · rcases hbool i s with h0 | h1
      · simp [inv, h0]
      · exact absurd h1 ha
  have hsum : ∑ i ∈ Finset.range N, ∑ s ∈ Finset.range 3, act i s * inv i s =
      limbVal b pubVal rhoExportPub := by
    have hrows := acc_rows b accSlotsX accExportBase rhoExportPub N A.hN envs
      (fun i hi g hm => A.gates i hi g (by
        simp only [vclGatesQ7, List.mem_append]; exact Or.inl (Or.inr hm)))
      A.shift A.first A.notLast A.last _ (by rw [A.pub])
    rw [← hrows]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < N := Finset.mem_range.mp hi
    rw [termVal_export]
    refine Finset.sum_congr rfl fun s _ => ?_
    rcases hbool i s with h0 | h1
    · have : actX (K := K) (envs i) s = 0 := by simpa [act, hi'] using h0
      rw [h0, this]; ring
    · have : actX (K := K) (envs i) s = 1 := by simpa [act, hi'] using h1
      simp [inv, h1, this]
  -- restrict to `s < 3`: `act` vanishes beyond
  exact reqIOFacts_of_rows N 3 act inv (fun i s => recX b (envs i) s)
    (FiniteIO.compress (coinsV b chalV γc ρc)) _ hbool
    (fun i s => by
      by_cases hs : s < 3
      · exact hinv i s hs
      · have h0 : act i s = 0 := by
          rcases s with _ | _ | _ | s
          · omega
          · omega
          · omega
          · by_cases hi : i < N <;> simp [act, hi, actX]
        simp [inv, h0])
    hsum

/-- **The path accumulator's `reqFacts`.** -/
def pathReqFactsQ7 (b : Basis (Fin 3) F K) (γc ρc n N : ℕ) (envs : ℕ → Env F) (chalV pubVal : ℕ → F)
    (A : AcceptedRowsQ7 b γc ρc n N envs chalV pubVal) :
    ReqIOFacts (FiniteIO.compress (m := 8) (coinsV b chalV γc ρc)) (limbVal b pubVal rhoPathPub) := by
  classical
  let act : ℕ → ℕ → K := fun i s => if i < N then actP (envs i) s else 0
  let inv : ℕ → ℕ → K := fun i s => if act i s = 1 then invVal b (envs i) (invBaseP s) else 0
  have hbool : ∀ i s, act i s = 0 ∨ act i s = 1 := by
    intro i s
    by_cases hi : i < N
    · obtain ⟨st, hst⟩ := A.sel i hi
      simp only [act, hi, if_true]; exact actP_bool _ st hst s
    · left; simp [act, hi]
  have hinv : ∀ i s, s < 2 → inv i s *
      FiniteIO.compress (coinsV b chalV γc ρc) (recP b (envs i) s) = act i s := by
    intro i s hs
    by_cases ha : act i s = 1
    · have hi : i < N := by by_contra hi; simp [act, hi] at ha
      obtain ⟨st, hst⟩ := A.sel i hi
      have ha' : actP (K := K) (envs i) s = 1 := by simpa [act, hi] using ha
      simp only [inv, ha, if_true]
      rw [← coinsAt_eq b γc ρc (envs i) chalV (A.chal i)]
      exact path_invQ7 b γc ρc n (envs i) st hst (A.gates i hi) s hs ha'
    · rcases hbool i s with h0 | h1
      · simp [inv, h0]
      · exact absurd h1 ha
  have hsum : ∑ i ∈ Finset.range N, ∑ s ∈ Finset.range 2, act i s * inv i s =
      limbVal b pubVal rhoPathPub := by
    have hrows := acc_rows b accSlotsP accPathBase rhoPathPub N A.hN envs
      (fun i hi g hm => A.gates i hi g (by
        simp only [vclGatesQ7, List.mem_append]; exact Or.inr hm))
      A.shift A.first A.notLast A.last _ (by rw [A.pub])
    rw [← hrows]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < N := Finset.mem_range.mp hi
    rw [termVal_path]
    refine Finset.sum_congr rfl fun s _ => ?_
    rcases hbool i s with h0 | h1
    · have : actP (K := K) (envs i) s = 0 := by simpa [act, hi'] using h0
      rw [h0, this]; ring
    · have : actP (K := K) (envs i) s = 1 := by simpa [act, hi'] using h1
      simp [inv, h1, this]
  exact reqIOFacts_of_rows N 2 act inv (fun i s => recP b (envs i) s)
    (FiniteIO.compress (coinsV b chalV γc ρc)) _ hbool
    (fun i s => by
      by_cases hs : s < 2
      · exact hinv i s hs
      · have h0 : act i s = 0 := by
          rcases s with _ | _ | s
          · omega
          · omega
          · by_cases hi : i < N <;> simp [act, hi, actP]
        simp [inv, h0])
    hsum


end facts

section chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **The one-hot state in `𝔽` from the gates** of `computeChipVCLE` at a row. -/
theorem selAt_of_gatesQ7 [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) (env : Env F)
    (hg : ∀ g ∈ vclGatesQ7 n b γc ρc, g.eval env = 0)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1) : ∃ st, SelAt env st := by
  have hs := VclSourceObligationsQ7.of_vclGatesQ7 n b γc ρc env hg
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

/-- **Acceptance gives an accepted row family**, hence the chip's `reqFacts`. -/
theorem acceptedRowsQ7_of_sat [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (γc ρc : ℕ)
    (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin 232 → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (computeChipVCLQ7 hn nodes b γc ρc chalV pubVal orbit) P)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1) :
    AcceptedRowsQ7 b γc ρc n n (rowEnvs (h := h) nodes orbit.ω P chalV pubVal) chalV pubVal := by
  have hs := (computeChipVCLQ7_sat_iff hn nodes b γc ρc chalV pubVal orbit P).1 hP
  have hmem : ∀ i (hi : i < n), nodes ⟨i, hi⟩ ∈ rowNodeSet nodes := fun i hi => by simp [rowNodeSet]
  have henv : ∀ i (hi : i < n), rowEnvs (h := h) nodes orbit.ω P chalV pubVal i =
      envOfTrace P orbit.ω (nodes ⟨i, hi⟩) chalV pubVal := fun i hi => by simp [rowEnvs, hi]
  have hgates : ∀ i < n, ∀ g ∈ vclGatesQ7 n b γc ρc,
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
    exact selAt_of_gatesQ7 n b γc ρc _ (hgates i hi) hchar
  · intro i; simp only [rowEnvs]; split_ifs <;> rfl
  · intro i; simp only [rowEnvs]; split_ifs <;> rfl


/-- **The IO coins at `frameVCL`**: the chip's denominators at `computeChipQ7` read the frame's IO
coins `(γ₀, ρ₀)` (`chalVQ7_io`). -/
theorem coinsV_chalVQ7 (b : Basis (Fin 3) F K) (χ : Coins frameVCL K) :
    coinsV b (chalVQ7 b χ) 21 24 = ⟨χ ioγVCL.1, χ ioρVCL.1⟩ := by
  simp only [coinsV]
  congr 1
  · simp_rw [fun k : Fin 3 => (chalVQ7_io b χ k).1]
    exact reconstruct_coord b _
  · simp_rw [fun k : Fin 3 => (chalVQ7_io b χ k).2]
    exact reconstruct_coord b _

end chip

end

end VclL.Compute
end Nock.NockVMROM.Thm54
