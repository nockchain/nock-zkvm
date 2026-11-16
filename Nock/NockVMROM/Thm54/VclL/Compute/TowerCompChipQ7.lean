import Nock.NockVMROM.Thm54.VclL.Compute.TowerSummandsQ7
import Nock.NockVMROM.Thm54.VclL.Compute.CompTreeVCL

/-!
# GEN-C5 steps 2-3: the tower CompChip wrapper, `reqFacts`, records, tree

-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Walk Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7
open Nock.NockVMROM.Thm54.VclL.Compute.NodeRecQ7
open Nock.ComputeTable (State DTcomp)
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.VclL.Compute.CoreQ7 Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Compute.CompChipVCL
open Nock.NockVMROM.Thm54.VclL.Compute.CompTreeVCL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (seedSpecVCL)
open Nock.NockVMROM.Thm54.VclL.Chips (ioSpecVCLQuad ioSpecVCLQuad_round)
open Nock.NockVMROM.Thm54.VclL.Compute.SummandsQ7
open Nock.NockVMROM.Thm54.SVWalk
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.ComputeWalkSeed Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.ComputePaperPacking (OneHotSelector)
open Nock.NockVMROM.Thm54.Unhosted309 (goodSrc physOf physOf_good_round varVal)
open Nock.NockVMROM.Thm54.VclL.Compute.TopoQ7 (lnPatch_pub_sfe)

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. The rejecting tower chip -/

section Reject
variable {F : Type} [Field F]

/-- The rejecting RAP: one gate `1 = 0`, at the tower width. -/
def rejectRAPT {h : ℕ} (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) (H : Finset F) : RAP F :=
  { e := 3
    k := 2
    wRAP := ![vclRound0, 202]
    w := vclWidthT
    w_eq := by simp [Fin.sum_univ_two, vclRound0, vclWidthT]
    h := h
    d := 4
    s := 1
    ω := orbit.ω
    β := orbit.βcoset
    I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
    C := fun _ => coeffToMv chalV pubVal (CoeffExpr.const 1)
    C_vars := fun _ => coeffToMv_vars chalV pubVal _
    C_deg := fun _ => (coeffToMv_totalDegree_le chalV pubVal _).trans (by simp [CoeffExpr.degree])
    H := H
    β_ne_zero := orbit.βcoset_ne_zero
    I_bound := by
      intro q hq
      have hq2 : q.2 = 0 ∨ q.2 = 1 := by
        have h2 := (Finset.mem_product.mp hq).2
        simpa [Finset.mem_insert, Finset.mem_singleton] using h2
      have hge : 2 ≤ 2 ^ h := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) orbit.h_pos
      rcases hq2 with hq' | hq' <;> rw [hq'] <;> omega }

/-- **The rejecting tower chip** (same preprocessing as `computeChipVCLQ7T`). -/
def rejectChipT {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) : FixedPreprocessingRAP F where
  rap := rejectRAPT chalV pubVal orbit (rowNodeSet nodes)
  rounds_pos := by norm_num [rejectRAPT]
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨11 + (j : ℕ), by
          have := j.isLt
          change 11 + (j : ℕ) < vclRound0
          simp only [vclRound0]
          omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

/-- **The rejecting tower chip accepts nothing.** -/
theorem rejectChipT_unsat {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (rejectChipT hn nodes chalV pubVal orbit).rap.w → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (rejectChipT hn nodes chalV pubVal orbit) P) : False := by
  have hx : nodes ⟨0, hn⟩ ∈ rowNodeSet nodes := by simp [rowNodeSet]
  have hz := hP.1 ⟨0, by change 0 < 1; norm_num⟩ _ hx
  have key : ((rejectChipT hn nodes chalV pubVal orbit).rap.compose P ⟨0, by change 0 < 1; norm_num⟩).eval
      (nodes ⟨0, hn⟩) = (CoeffExpr.const (1 : F)).eval (Reify.envOfTrace P orbit.ω (nodes ⟨0, hn⟩) chalV pubVal) := by
    rw [Reify.compose_eval]
    exact eval_coeffToMv P orbit.ω (nodes ⟨0, hn⟩) chalV pubVal _
  rw [key] at hz
  simp [CoeffExpr.eval] at hz

end Reject


/-! ## 2. The CF chip at the tower -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [CharP K (ringChar K)] [DecidableEq F] {hC : ℕ} {S : MemShape}
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **What the tower CF chip enforces**: exactly `GoodCF`'s checks.  (The Form R λ-exponent is the
separate parameter `e := pwScaleExp K` of `vclGatesQ7T`, so there is no `N = pwScaleExp K` conjunct:
the chip accepts runs of any row count `N ≤ char`.) -/
def GoodCFT (V : VerifierData F K hC S) (ρ : Fin 3 → Quad (algebraMap F K δ)) : Prop :=
  V.AdjacentC ∧ Function.Injective V.computeNodes ∧ (∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1) ∧
    V.N ≤ ringChar K ∧ ρ 0 = 0

open Classical in
/-- **The tower CF chip.** -/
def chipCFT (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → Quad (algebraMap F K δ))
    (χ : Coins frameVCL K) : FixedPreprocessingRAP F :=
  if GoodCFT δ V ρ then
    computeChipVCLQ7T V.hN V.computeNodes V.basis δ (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ) V.orbitC
  else
    rejectChipT V.hN V.computeNodes (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ) V.orbitC

theorem chipCFT_width (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → Quad (algebraMap F K δ))
    (χ : Coins frameVCL K) : (chipCFT δ V x ρ χ).rap.w = (tableVCLT hC).width := by
  unfold chipCFT; split_ifs <;> rfl

theorem chipCFT_good (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → Quad (algebraMap F K δ))
    (χ : Coins frameVCL K) (Q : Fin (tableVCLT hC).width → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (chipCFT δ V x ρ χ)
      (fun j => Q (Fin.cast (chipCFT_width δ V x ρ χ) j))) : GoodCFT δ V ρ := by
  by_contra hng
  have hc : chipCFT δ V x ρ χ = rejectChipT V.hN V.computeNodes (chalVQ7T δ V.basis χ)
      (pubCFT δ V x ρ χ) V.orbitC := by
    unfold chipCFT; exact if_neg hng
  have key : ∀ c : FixedPreprocessingRAP F, c = rejectChipT V.hN V.computeNodes (chalVQ7T δ V.basis χ)
      (pubCFT δ V x ρ χ) V.orbitC → ∀ P : Fin c.rap.w → F[X],
      RAP.SatisfiesWithPreprocessing c P → False := by
    intro c hc P hP
    subst hc
    exact rejectChipT_unsat _ _ _ _ _ P hP
  exact key _ hc _ hP

theorem chipCFT_sat (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → Quad (algebraMap F K δ))
    (χ : Coins frameVCL K) (Q : Fin (tableVCLT hC).width → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (chipCFT δ V x ρ χ)
      (fun j => Q (Fin.cast (chipCFT_width δ V x ρ χ) j))) :
    RAP.SatisfiesWithPreprocessing
      (computeChipVCLQ7T V.hN V.computeNodes V.basis δ (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ) V.orbitC)
      Q := by
  have hg := chipCFT_good δ V x ρ χ Q hP
  have hc : chipCFT δ V x ρ χ = computeChipVCLQ7T V.hN V.computeNodes V.basis δ (chalVQ7T δ V.basis χ)
      (pubCFT δ V x ρ χ) V.orbitC := by
    unfold chipCFT; exact if_pos hg
  have key : ∀ c : FixedPreprocessingRAP F, c = computeChipVCLQ7T V.hN V.computeNodes V.basis δ
      (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ) V.orbitC → ∀ hw : c.rap.w = (tableVCLT hC).width,
      RAP.SatisfiesWithPreprocessing c (fun j => Q (Fin.cast hw j)) →
      RAP.SatisfiesWithPreprocessing (computeChipVCLQ7T V.hN V.computeNodes V.basis δ
        (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ) V.orbitC) Q := by
    intro c hc hw hP
    subst hc
    have hfun : (fun j => Q (Fin.cast hw j)) = Q := funext fun j => rfl
    rw [hfun] at hP
    exact hP
  exact key _ hc _ hP

end Chip

/-! ## 3. Accepted rows at the tower chip -/

section Acc
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [CharP K (ringChar K)] [DecidableEq F]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

theorem acceptedRowsQ7T_of_sat {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit).rap.w → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit) P)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i) :
    AcceptedRowsQ7T δ b n n (rowEnvs (h := h) nodes orbit.ω P chalV pubVal) chalV pubVal := by
  have hs := (computeChipVCLQ7T_sat_iff hn nodes b δ chalV pubVal orbit P).1 hP
  have hmem : ∀ i (hi : i < n), nodes ⟨i, hi⟩ ∈ rowNodeSet nodes := fun i hi => by simp [rowNodeSet]
  have henv : ∀ i (hi : i < n), rowEnvs (h := h) nodes orbit.ω P chalV pubVal i =
      envOfTrace P orbit.ω (nodes ⟨i, hi⟩) chalV pubVal := fun i hi => by simp [rowEnvs, hi]
  have hgates : ∀ i < n, ∀ g ∈ vclGatesQ7T n (MemoryTable.pwScaleExp K) b δ,
      g.eval (rowEnvs (h := h) nodes orbit.ω P chalV pubVal i) = 0 := by
    intro i hi g hg
    rw [henv i hi]; exact hs.2 _ (hmem i hi) g hg
  have h11 : (11 : ℕ) < (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit).rap.w := by
    change 11 < 410; norm_num
  have h12 : (12 : ℕ) < (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit).rap.w := by
    change 12 < 410; norm_num
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
  refine ⟨hn, hgates, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro i; simp only [rowEnvs]; split_ifs <;> rfl
  · intro i; simp only [rowEnvs]; split_ifs <;> rfl

end Acc


/-! ## 4. The committed tower records read round `≤ 1` columns only -/

section Recs
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [DecidableEq F] {hC : ℕ} {S : MemShape}
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- A physical column of round `≤ 1` of the tower table. -/
def ColOkT (c : ℕ) : Prop := (c < 388 ∨ c = z1Col) ∧ (c < 232 → colRoundVCLE c ≤ 1)

instance (c : ℕ) : Decidable (ColOkT c) := by unfold ColOkT; infer_instance

/-- An entry reads (Re limbs and Im limbs) only `ColOkT` columns. -/
def entryOkT : Entry → Bool
  | .k l => (List.range 3).all (fun j => decide (ColOkT (l + j))) &&
      (imColOfLimb l).elim true (fun c => (List.range 3).all fun j => decide (ColOkT (c + j)))
  | .f c => decide (ColOkT c)

theorem formulaRecT_ok : ∀ i, entryOkT (formulaRec i) = true := by decide +kernel
theorem tailRecT_ok : ∀ i, entryOkT (tailRec i) = true := by decide +kernel
theorem ttRecT_ok : ∀ i, entryOkT (ttRec i) = true := by decide +kernel
theorem op0PathRecT_ok : ∀ i, entryOkT (op0PathRec i) = true := by decide +kernel
theorem op9PathRecT_ok : ∀ i, entryOkT (op9PathRec i) = true := by decide +kernel

theorem qEntry_congr (b : Basis (Fin 3) F K) (eF eF' : Env F)
    (hc : ∀ c, ColOkT c → eF.trace c = eF'.trace c) (e : Entry) (he : entryOkT e = true) :
    Q.val δ (entryQ F e) (gatherEnv b eF) eF = Q.val δ (entryQ F e) (gatherEnv b eF') eF' := by
  cases e with
  | k l =>
    simp only [entryOkT, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at he
    obtain ⟨he1, he2⟩ := he
    simp only [entryQ, qvar_val, kread, gatherEnv]
    have hre : LogUp.limbVal b eF.trace l = LogUp.limbVal b eF'.trace l := by
      unfold LogUp.limbVal
      exact Finset.sum_congr rfl fun j _ => by rw [hc (l + j) (he1 j j.isLt)]
    have him : imVal (LogUp.limbVal b eF.trace) (imColOfLimb l) =
        imVal (LogUp.limbVal b eF'.trace) (imColOfLimb l) := by
      cases hx : imColOfLimb l with
      | none => rfl
      | some c =>
        rw [hx] at he2
        simp only [Option.elim, List.all_eq_true, List.mem_range, decide_eq_true_eq] at he2
        simp only [imVal, LogUp.limbVal]
        exact Finset.sum_congr rfl fun j _ => by rw [hc (c + j) (he2 j j.isLt)]
    rw [hre, him]
  | f c =>
    simp only [entryOkT, decide_eq_true_eq] at he
    simp only [entryQ, qlift_val]
    exact congrArg (fun x => algebraMap F (Quad (algebraMap F K δ)) x) (hc c he)

theorem recValQ_congr (b : Basis (Fin 3) F K) (eF eF' : Env F)
    (hc : ∀ c, ColOkT c → eF.trace c = eF'.trace c) {m : ℕ} (r : Fin m → Entry)
    (hr : ∀ i, entryOkT (r i) = true) :
    recValQ δ (gatherEnv b eF) eF r = recValQ δ (gatherEnv b eF') eF' r :=
  funext fun i => qEntry_congr δ b eF eF' hc _ (hr i)

theorem recXQ_congr (b : Basis (Fin 3) F K) (eF eF' : Env F)
    (hc : ∀ c, ColOkT c → eF.trace c = eF'.trace c) (s : ℕ) :
    recXQ δ (gatherEnv b eF) eF s = recXQ δ (gatherEnv b eF') eF' s := by
  rcases s with _ | _ | s
  · funext c
    simp only [recXQ, recQ0]
    split_ifs with h
    · exact qEntry_congr δ b eF eF' hc _ (formulaRecT_ok ⟨c, h⟩)
    · rfl
  · simp only [recXQ]
    rw [recValQ_congr δ b eF eF' hc _ tailRecT_ok]
  · simp only [recXQ]
    rw [recValQ_congr δ b eF eF' hc _ ttRecT_ok]

theorem recPQ_congr (b : Basis (Fin 3) F K) (eF eF' : Env F)
    (hc : ∀ c, ColOkT c → eF.trace c = eF'.trace c) (s : ℕ) :
    recPQ δ (gatherEnv b eF) eF s = recPQ δ (gatherEnv b eF') eF' s := by
  rcases s with _ | s
  · exact recValQ_congr δ b eF eF' hc _ op0PathRecT_ok
  · exact recValQ_congr δ b eF eF' hc _ op9PathRecT_ok

theorem selOkT (c : ℕ) (hc : c < 13) : ColOkT c :=
  ⟨Or.inl (by omega), fun _ => sel_round_le1 c hc⟩

theorem z1OkT : ColOkT z1Col := ⟨Or.inr rfl, fun h => absurd h (by decide)⟩

theorem actXQ_congr (eF eF' : Env F)
    (hc : ∀ c, ColOkT c → eF.trace c = eF'.trace c) (s : ℕ) :
    actXQ (K := K) δ eF s = actXQ (K := K) δ eF' s := by
  rcases s with _ | _ | _ | s
  · rfl
  · simp only [actXQ, selSum_eval, slot1ExportSels, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    rw [hc 2 (selOkT _ (by norm_num)), hc 5 (selOkT _ (by norm_num)),
      hc 6 (selOkT _ (by norm_num)), hc 7 (selOkT _ (by norm_num)),
      hc 8 (selOkT _ (by norm_num)), hc 9 (selOkT _ (by norm_num))]
  · simp only [actXQ]; rw [hc 6 (selOkT _ (by norm_num))]
  · rfl

theorem actPQ_congr (eF eF' : Env F)
    (hc : ∀ c, ColOkT c → eF.trace c = eF'.trace c) (s : ℕ) :
    actPQ (K := K) δ eF s = actPQ (K := K) δ eF' s := by
  rcases s with _ | _ | s
  · simp only [actPQ]; rw [hc 0 (selOkT _ (by norm_num)), hc z1Col z1OkT]
  · simp only [actPQ]; rw [hc 9 (selOkT _ (by norm_num)), hc z1Col z1OkT]
  · rfl

theorem rowEnvsT_trace_round (V : VerifierData F K hC S) (c1 p1 c2 p2 : ℕ → F)
    (Q Q' : Fin (tableVCLT hC).width → F[X]) (hQ : AgreeT Q Q') (i : ℕ) :
    ∀ c, ColOkT c →
      (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q c1 p1 i).trace c =
        (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q' c2 p2 i).trace c := by
  intro c hc
  have hw : c < (tableVCLT hC).width := by
    show c < 410
    rcases hc.1 with h | h <;> (try simp only [z1Col] at h) <;> omega
  have hr : (tableVCLT hC).colRound ⟨c, hw⟩ ≤ 1 := by
    by_cases h232 : c < 232
    · rw [tableVCLT_colRound_lt hC c h232 hw]; exact hc.2 h232
    · rcases hc.1 with h | h
      · rw [tableVCLT_colRound_im hC c (by omega) h hw]
      · subst h; rw [tableVCLT_colRound_z1 hC hw]
  simp only [rowEnvs]
  split_ifs <;> simp only [envOfTrace] <;> split_ifs with h
  all_goals first | rfl | rw [hQ ⟨c, hw⟩ hr]

/-- **The committed request records read only columns of round `≤ 1`** (no coin, no public). -/
theorem reqRecsT_round (V : VerifierData F K hC S) (c1 p1 c2 p2 : ℕ → F)
    (Q Q' : Fin (tableVCLT hC).width → F[X]) (hQ : AgreeT Q Q') (a : Fin 3) :
    reqRecsQ7G (towerReader δ V.basis) V c1 p1 Q a = reqRecsQ7G (towerReader δ V.basis) V c2 p2 Q' a := by
  have ht := rowEnvsT_trace_round V c1 p1 c2 p2 Q Q' hQ
  fin_cases a
  · rfl
  · show exportRecsQ7G (towerReader δ V.basis) V c1 p1 Q = exportRecsQ7G (towerReader δ V.basis) V c2 p2 Q'
    unfold exportRecsQ7G
    congr 1
    · funext i s
      split_ifs
      · exact actXQ_congr δ _ _ (ht i) s
      · rfl
    · funext i s
      exact recXQ_congr δ V.basis _ _ (ht i) s
  · show pathRecsQ7G (towerReader δ V.basis) V c1 p1 Q = pathRecsQ7G (towerReader δ V.basis) V c2 p2 Q'
    unfold pathRecsQ7G
    congr 1
    · funext i s
      split_ifs
      · exact actPQ_congr δ _ _ (ht i) s
      · rfl
    · funext i s
      exact recPQ_congr δ V.basis _ _ (ht i) s

end Recs


/-! ## 5. `reqFacts`, `reqRecords` and the bounds at the tower -/

section ReqF
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [CharP K (ringChar K)] [DecidableEq F] {hC : ℕ} {S : MemShape}
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **The tower CF's `reqFacts`**: validity `ρ 0 = 0` (no records); export / path from the accepted tower
row family, transported to the `𝕂′` IO coins `((χ4,χ6),(χ5,χ7))` and the terminals `ρ 1`, `ρ 2`. -/
def reqFactsCFT (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → Quad (algebraMap F K δ))
    (χ : Coins frameVCL K) (Q : Fin (tableVCLT hC).width → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (chipCFT δ V x ρ χ)
      (fun j => Q (Fin.cast (chipCFT_width δ V x ρ χ) j))) :
    ∀ a : Fin 3, ReqIOFacts (FiniteIO.compress (m := RV.mVCL a)
      ((ioSpecVCLQuad (algebraMap F K δ)).ioCoins χ)) (ρ a) :=
  have hg := chipCFT_good δ V x ρ χ Q hP
  have hs := chipCFT_sat δ V x ρ χ Q hP
  let A := acceptedRowsQ7T_of_sat δ V.hN V.computeNodes V.basis (chalVQ7T δ V.basis χ)
    (pubCFT δ V x ρ χ) V.orbitC Q hs hg.2.1 hg.1
  fun a => match a with
  | ⟨0, _⟩ => ⟨[], by simp [hg.2.2.2.2], fun r hr => absurd hr (List.not_mem_nil)⟩
  | ⟨1, _⟩ => castReq (exportReqFactsQ7T V.N V.N
      (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ))
      (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ) A hg.2.2.1
      ((ioSpecVCLQuad (algebraMap F K δ)).ioCoins χ)
      (fun i _ => coinsQ_chalVQ7T δ V.basis χ _ (A.chal i)))
      rfl (limbVal_pubCFT_export δ χ V x ρ)
  | ⟨2, _⟩ => castReq (pathReqFactsQ7T V.N V.N
      (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ))
      (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ) A hg.2.2.1
      ((ioSpecVCLQuad (algebraMap F K δ)).ioCoins χ)
      (fun i _ => coinsQ_chalVQ7T δ V.basis χ _ (A.chal i)))
      rfl (limbVal_pubCFT_path δ χ V x ρ)

/-- **The tower CF's `reqRecords`**: the committed records, a function of the columns alone. -/
def reqRecordsCFT (V : VerifierData F K hC S) (_x : ℕ → F) (Q : Fin (tableVCLT hC).width → F[X])
    (_χ : Coins frameVCL K) : ∀ a : Fin 3, List (Fin (RV.mVCL a) → Quad (algebraMap F K δ)) :=
  reqRecsQ7G (towerReader δ V.basis) V (fun _ => 0) (fun _ => 0) Q

theorem reqFactsCFT_records (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → Quad (algebraMap F K δ))
    (χ : Coins frameVCL K) (Q : Fin (tableVCLT hC).width → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (chipCFT δ V x ρ χ)
      (fun j => Q (Fin.cast (chipCFT_width δ V x ρ χ) j))) (a : Fin 3) :
    (reqFactsCFT δ V x ρ χ Q hP a).records = reqRecordsCFT δ V x Q χ a := by
  fin_cases a
  · rfl
  · refine (castReq_records _ _ _).trans ?_
    exact reqRecsT_round δ V _ _ _ _ Q Q (fun _ _ => rfl) 1
  · refine (castReq_records _ _ _).trans ?_
    exact reqRecsT_round δ V _ _ _ _ Q Q (fun _ _ => rfl) 2

theorem actPQ_excl (env : Env F) (st : State) (h : SelAt env st) :
    ¬ (actPQ (K := K) δ env 0 = 1 ∧ actPQ (K := K) δ env 1 = 1) := by
  rintro ⟨h0, h1⟩
  have ht := selAt_trace h
  simp only [actPQ] at h0 h1
  have e0 : env.trace 0 * (1 - env.trace z1Col) = 1 :=
    (algebraMap F (Quad (algebraMap F K δ))).injective (by rw [h0]; exact (map_one _).symm)
  have e1 : env.trace 9 * (1 - env.trace z1Col) = 1 :=
    (algebraMap F (Quad (algebraMap F K δ))).injective (by rw [h1]; exact (map_one _).symm)
  rw [ht 0 (by norm_num)] at e0
  rw [ht 9 (by norm_num)] at e1
  cases st <;> simp [selIdx] at e0 e1

theorem reqRecsT_length_le (V : VerifierData F K hC S) (chalV pubVal : ℕ → F)
    (Q : Fin (tableVCLT hC).width → F[X])
    (hsel : ∀ i < V.N, ∃ st, SelAt (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) st)
    (a : Fin 3) : (reqRecsQ7G (towerReader δ V.basis) V chalV pubVal Q a).length ≤ reqBoundCF V a := by
  fin_cases a
  · show ([] : List (Fin 5 → Quad (algebraMap F K δ))).length ≤ 0
    simp
  · show (exportRecsQ7G (towerReader δ V.basis) V chalV pubVal Q).length ≤ 3 * V.N
    have := activeRecords_length_le (Kio := Quad (algebraMap F K δ)) V.N 3
      (fun i s => if i < V.N then
        actXQ δ (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s else 0)
      (fun i s => recXQ δ (gatherEnv V.basis (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i))
        (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s)
    unfold exportRecsQ7G
    exact this.trans (by omega)
  · show (pathRecsQ7G (towerReader δ V.basis) V chalV pubVal Q).length ≤ V.N
    unfold pathRecsQ7G
    refine activeRecords_two_le V.N _ _ fun i => ?_
    by_cases hi : i < V.N
    · obtain ⟨st, hst⟩ := hsel i hi
      simp only [hi, if_true]
      exact actPQ_excl δ _ st hst
    · simp [hi]

theorem reqFactsCFT_length (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → Quad (algebraMap F K δ))
    (χ : Coins frameVCL K) (Q : Fin (tableVCLT hC).width → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (chipCFT δ V x ρ χ)
      (fun j => Q (Fin.cast (chipCFT_width δ V x ρ χ) j))) (a : Fin 3) :
    (reqFactsCFT δ V x ρ χ Q hP a).records.length ≤ reqBoundCF V a := by
  rw [reqFactsCFT_records]
  have hg := chipCFT_good δ V x ρ χ Q hP
  have hs := chipCFT_sat δ V x ρ χ Q hP
  have hsat := (computeChipVCLQ7T_sat_iff V.hN V.computeNodes V.basis δ (chalVQ7T δ V.basis χ)
    (pubCFT δ V x ρ χ) V.orbitC Q).1 hs
  have hsel : ∀ i < V.N, ∃ st, SelAt (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q
      (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ) i) st := by
    intro i hi
    have henv : rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ) i =
        envOfTrace Q V.orbitC.ω (V.computeNodes ⟨i, hi⟩) (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ) := by
      simp [rowEnvs, hi]
    rw [henv]
    exact selAt_of_towerRow δ V.basis V.N _
      (hsat.2 _ (by simp [rowNodeSet])) hg.2.2.1
  have h1 := reqRecsT_length_le δ V (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ) Q hsel a
  have h2 := reqRecsT_round δ V (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ) (fun _ => 0) (fun _ => 0) Q Q
    (fun _ _ => rfl) a
  unfold reqRecordsCFT
  rw [← h2]
  exact h1

end ReqF


/-! ## 6. The tower tree: publics-free, the root label -/

section Tree
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [CharP K (ringChar K)] [DecidableEq F] {hC : ℕ} {S : MemShape}
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

theorem envsVG_pub_irrel_T (V : VerifierData F K hC S) (c p p' : ℕ → F)
    (Q : Fin (tableVCLT hC).width → F[X])
    (hp : ∀ j, j < 42 ∨ (48 ≤ j ∧ j < 51) → p j = p' j) (i : Fin V.N) :
    envsVG (towerGather δ V.basis) V c p Q i = envsVG (towerGather δ V.basis) V c p' Q i := by
  unfold envsVG
  simp only [towerGather, towerEnv309, towerEnv, gatherEnv, pullEnv, envOfTrace]
  congr 1
  · funext n
    simp only [imVal]
    have e1 : LogUp.limbVal V.basis p (3 * (n : ℕ)) = LogUp.limbVal V.basis p' (3 * (n : ℕ)) :=
      limbVal_congr_T V.basis p p' _ (fun k hk => hp _ (Or.inl (by have := n.isLt; omega)))
    rw [e1]
    cases hx : towerM.extPub n with
    | none => rfl
    | some c0 =>
      have hc0 : c0 = 48 := by
        have h3 : ∀ m : Fin 3, (fullImMap.extPub m).elim true (fun c => decide (c = 48)) = true := by decide
        have := h3 n
        rw [show fullImMap.extPub n = some c0 from hx] at this
        simpa using this
      subst hc0
      simp only
      rw [limbVal_congr_T V.basis p p' 48 (fun k hk => hp _ (Or.inr (by omega)))]
  · funext n
    exact hp _ (Or.inl (by have := n.isLt; omega))



theorem treeVG_pub_irrel_T (V : VerifierData F K hC S) (c p p' : ℕ → F)
    (Q : Fin (tableVCLT hC).width → F[X])
    (hp : ∀ j, j < 42 ∨ (48 ≤ j ∧ j < 51) → p j = p' j) :
    treeVG (towerGather δ V.basis) V c p Q = treeVG (towerGather δ V.basis) V c p' Q := by
  have h : envsPG (towerGather δ V.basis) V c p Q = envsPG (towerGather δ V.basis) V c p' Q :=
    funext fun i => by unfold envsPG; rw [envsVG_pub_irrel_T δ V c p p' Q hp i]
  simp only [treeVG, treeV1G, h]

end Tree

/-- **The root label of `treeVG` is row `0`'s** (carrier doubled), at any gather. -/
theorem treeVG_label_root {F K K' : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [DecidableEq F] [DecidableEq K] {hC : ℕ} {S : MemShape}
    [Field K'] [Algebra F K'] [FiniteDimensional F K'] [DecidableEq K'] {w : ℕ}
    (G : CoordGather F K') (V : VerifierData F K hC S) (c p : ℕ → F) (Q : Fin w → F[X]) :
    (treeVG G V c p Q).label = (rowLabel (envsPG G V c p Q ⟨0, V.hN⟩),
      2 * rowCarrier (envsPG G V c p Q ⟨0, V.hN⟩)) := by
  unfold treeVG treeV1G computeTree treeOfRows reconTree
  rw [label_mapNTree, buildT_label]
  simp only [at1]
  rw [dif_pos (show 1 - 1 < V.N from by have := V.hN; omega), dif_pos (show 1 - 1 < V.N from by have := V.hN; omega),
    dif_pos (show 1 - 1 < V.N from by have := V.hN; omega)]

/-! ## 7. `node_records` and `root_binds` at the tower CF chip -/

section Fam
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [CharP K (ringChar K)] [DecidableEq F] [Fintype F] {hC : ℕ} {S : MemShape}
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

theorem sumZeroT_mem (tr : Traces F (tableVCLT hC) S) (χ : Coins frameVCL K) :
    (sumZeroT δ : TSummand F K hC S).mem tr χ ↔ zQuad δ χ = 0 := by
  unfold sumZeroT zeroSummand
  rw [seedSummand_mem]
  simp only [Finset.mem_singleton]
  exact Iff.rfl

theorem sumTilingT_mem (V : VerifierData F K hC S) (tr : Traces F (tableVCLT hC) S) (χ : Coins frameVCL K) :
    (sumTilingT δ V).mem tr χ ↔
      algebraMap K (Quad (algebraMap F K δ)) (χ ⟨0, by decide⟩) ∈ tilingSetE (srcZT δ V tr.1) V.hN := by
  unfold sumTilingT; erw [coinSummand_mem, mem_pullSet]

theorem sumAlphaRootT_mem (V : VerifierData F K hC S) (tr : Traces F (tableVCLT hC) S) (χ : Coins frameVCL K) :
    (sumAlphaRootT δ V).mem tr χ ↔
      algebraMap K (Quad (algebraMap F K δ)) (χ ⟨0, by decide⟩) ∈ alphaSetE (srcZT δ V tr.1) V.hN
        (algebraMap K (Quad (algebraMap F K δ)) (χ ⟨1, by decide⟩)) (claimLabelVec (zQuad δ χ) V.claim) := by
  unfold sumAlphaRootT; erw [coinSummand_mem, mem_pullSet]

theorem sumGammaRootT_mem (V : VerifierData F K hC S) (tr : Traces F (tableVCLT hC) S) (χ : Coins frameVCL K) :
    (sumGammaRootT δ V).mem tr χ ↔
      algebraMap K (Quad (algebraMap F K δ)) (χ ⟨1, by decide⟩) ∈
        gammaSetE (srcZT δ V tr.1) V.hN (claimLabelVec (zQuad δ χ) V.claim) := by
  unfold sumGammaRootT; erw [coinSummand_mem, mem_pullSet]

/-- The `z′` facts `node_records` takes, from outside `sumZeroT`. -/
theorem tower_z_facts (V : VerifierData F K hC S) (χ : Coins frameVCL K) (pubVal : ℕ → F)
    (hz : zQuad δ χ ≠ 0) :
    zQ (cdOfGG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ) pubVal) (chalVQ7T δ V.basis χ) ≠ 0 ∧
      (towerGather δ V.basis).chalSlot (chalVQ7T δ V.basis χ) 5 =
        (zQ (cdOfGG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ) pubVal) (chalVQ7T δ V.basis χ))⁻¹ := by
  have h1 : zQ (cdOfGG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ) pubVal) (chalVQ7T δ V.basis χ) =
      zQuad δ χ := chalSlot_one_T δ V.basis χ
  rw [h1]
  exact ⟨hz, chalSlot_five_T δ V.basis χ⟩

theorem hcharQ_of (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) :
    ∀ n : ℕ, n ≤ 11 → (n : Quad (algebraMap F K δ)) = 1 → n = 1 := by
  intro n hn h
  apply hchar n hn
  apply (algebraMap K (Quad (algebraMap F K δ))).injective
  rw [map_natCast, map_one]
  exact h

/-- **`node_records` at the tower CF chip** (the frame field's shape, `inlineRecords = 0`). -/
theorem node_records_CFT (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → Quad (algebraMap F K δ))
    (χ : Coins frameVCL K) (Q : Fin (tableVCLT hC).width → F[X])
    (h : RAP.SatisfiesWithPreprocessing (chipCFT δ V x ρ χ)
      (fun j => Q (Fin.cast (chipCFT_width δ V x ρ χ) j)))
    (Qm : ∀ t : Fin S.k, Fin (S.table t).width → F[X])
    (hout : ∀ s ∈ summandsQ7T δ V, ¬ s.mem (Q, Qm) χ)
    (u : NTree ((State × DTcomp (Quad (algebraMap F K δ))) × ℕ))
    (hu : InTree (treeVG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ)
      (pubVQ7T δ V.basis V.claim x χ) Q) u)
    (j : ℕ) (hj : j < Nock.Framework.recordCount u.label.1.1) :
    (∃ a : Fin 3, ∃ r ∈ (reqFactsCFT δ V x ρ χ Q h a).records,
      (RV.recordViewVCL F K (Quad (algebraMap F K δ)) (tableVCLT hC) S hC).root a r =
        (SVFrame.traceRecOf u.label j).root ∧
      (RV.recordViewVCL F K (Quad (algebraMap F K δ)) (tableVCLT hC) S hC).child a r =
        (SVFrame.traceRecOf u.label j).child ∧
      (RV.recordViewVCL F K (Quad (algebraMap F K δ)) (tableVCLT hC) S hC).key a r =
        recKeyQ7' V (b0 (T := tableVCLT hC) Q) u.label.1.1 u.label.2 j ∧
      (RV.recordViewVCL F K (Quad (algebraMap F K δ)) (tableVCLT hC) S hC).axis a V
          (b0 (T := tableVCLT hC) Q) (fun t => b0 (Qm t)) r =
        SVFrame.joinRecordAxis u.label.1.1 (axB0Q7 V (b0 (T := tableVCLT hC) Q)) u.label.2 j) ∨
    (((u.label.1.1 = .s0 ∧ j = 1) ∨ (u.label.1.1 = .s9 ∧ j = 2)) ∧
      SVFrame.joinRecordAxis u.label.1.1 (axB0Q7 V (b0 (T := tableVCLT hC) Q)) u.label.2 j = 1 ∧
      (SVFrame.traceRecOf u.label j).child = (SVFrame.traceRecOf u.label j).root) := by
  have hg := chipCFT_good δ V x ρ χ Q h
  have hs := chipCFT_sat δ V x ρ χ Q h
  have hout0 := hout (sumZeroT δ) (by simp [summandsQ7T])
  have hz0 : zQuad δ χ ≠ 0 := fun h0 => hout0 ((sumZeroT_mem δ _ χ).2 h0)
  obtain ⟨hz, hzi⟩ := tower_z_facts δ V χ (pubCFT δ V x ρ χ) hz0
  have hu' : InTree (treeVG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ) Q) u := by
    rw [treeVG_pub_irrel_T δ V _ (pubCFT δ V x ρ χ) (pubVQ7T δ V.basis V.claim x χ) Q
      (fun j hj => pubCFT_lt δ χ V x ρ j hj)]
    exact hu
  have hNp : V.N ≤ ringChar (Quad (algebraMap F K δ)) := by rw [ringChar_quad]; exact hg.2.2.2.1
  rcases towerNodeRecordsQ7 δ V (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ)
    Q hs hg.2.1 hg.2.2.1 (hcharQ_of δ hg.2.2.1) hz hzi hg.1 hNp (fun t => b0 (Qm t)) u hu' j hj with
    ⟨a, r, hr, h1, h2, h3, h4⟩ | hid
  swap
  · exact Or.inr hid
  refine Or.inl ⟨a, r, ?_, h1, h2, h3, h4⟩
  rw [reqFactsCFT_records]
  unfold reqRecordsCFT
  rw [← reqRecsT_round δ V (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ) (fun _ => 0) (fun _ => 0) Q Q
    (fun _ _ => rfl) a]
  exact hr


/-- **`root_binds` at the tower CF chip**: the root row's decoded `(s, f, e)` bind the claim at the
`𝕂′` seed `z′ = (χ2, χ3)`. -/
theorem root_binds_CFT (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → Quad (algebraMap F K δ))
    (χ : Coins frameVCL K) (Q : Fin (tableVCLT hC).width → F[X])
    (h : RAP.SatisfiesWithPreprocessing (chipCFT δ V x ρ χ)
      (fun j => Q (Fin.cast (chipCFT_width δ V x ρ χ) j)))
    (Qm : ∀ t : Fin S.k, Fin (S.table t).width → F[X])
    (hout : ∀ s ∈ summandsQ7T δ V, ¬ s.mem (Q, Qm) χ) :
    SemanticStrategy.bindFP (zQuad δ χ) V.claim.subject
        (treeVG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ)
          (pubVQ7T δ V.basis V.claim x χ) Q).label.1.2.2.1.s ∧
      SemanticStrategy.bindFP (zQuad δ χ) V.claim.formula
        (treeVG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ)
          (pubVQ7T δ V.basis V.claim x χ) Q).label.1.2.2.1.f ∧
      SemanticStrategy.bindFP (zQuad δ χ) V.claim.result
        (treeVG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ)
          (pubVQ7T δ V.basis V.claim x χ) Q).label.1.2.2.1.e := by
  have hg := chipCFT_good δ V x ρ χ Q h
  have hs := chipCFT_sat δ V x ρ χ Q h
  have RF := towerRowFactsQ7 δ V.hN V.computeNodes V.basis (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ)
    V.orbitC Q hs V.claim (pubCFT δ V x ρ χ) hg.2.1
  have nT := hout (sumTilingT δ V) (by simp [summandsQ7T])
  have nA := hout (sumAlphaRootT δ V) (by simp [summandsQ7T])
  have nG := hout (sumGammaRootT δ V) (by simp [summandsQ7T])
  rw [sumTilingT_mem] at nT
  rw [sumAlphaRootT_mem] at nA
  rw [sumGammaRootT_mem] at nG
  obtain ⟨st0, hst0, b1, b2, b3⟩ := root_binds_outsideG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ)
    (pubCFT δ V x ρ χ) Q hg.1 RF (hcharQ_of δ hg.2.2.1) (srcZT δ V Q)
    (fun i q hq => srcVT_good δ V (fun _ _ => rfl) _ _ _ _ i q hq)
    (algebraMap K (Quad (algebraMap F K δ)) (χ ⟨0, by decide⟩))
    (algebraMap K (Quad (algebraMap F K δ)) (χ ⟨1, by decide⟩)) (zQuad δ χ)
    (chalSlot_six_T δ V.basis χ) (chalSlot_ten_T δ V.basis χ) (pubSlot_zero_T δ χ V x ρ)
    (by
      have := pubSlot_one_T δ χ V x ρ
      exact this)
    nT nA nG
  rw [← treeVG_pub_irrel_T δ V _ (pubCFT δ V x ρ χ) (pubVQ7T δ V.basis V.claim x χ) Q
    (fun j hj => pubCFT_lt δ χ V x ρ j hj), treeVG_label_root]
  have hst : (rowLabel (envsPG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ) Q
      ⟨0, V.hN⟩)).1 = st0 := by
    have := rowStateOf_of_oneHot hst0
    rw [rowLabel_fst, ← rowStateOf_toSourceEnv]
    exact this
  have key := lnPatch_pub_sfe (envsVG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ)
    (pubCFT δ V x ρ χ) Q ⟨0, V.hN⟩) st0
  obtain ⟨-, hs', hf', he', -⟩ := key
  have hP : (rowLabel (envsPG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ) Q
      ⟨0, V.hN⟩)).2.2.1 =
      StrategyOfTracesLift.decodePub (lnPatch (envsVG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ)
        (pubCFT δ V x ρ χ) Q ⟨0, V.hN⟩)) st0 := by
    show StrategyOfTracesLift.decodePub _ (StrategyOfTracesLift.computeStateOf _) = _
    rw [show StrategyOfTracesLift.computeStateOf (StrategyOfTracesLift.decodeSource
      (envsPG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ) (pubCFT δ V x ρ χ) Q ⟨0, V.hN⟩)) = st0 from hst]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · show SemanticStrategy.bindFP _ _ (rowLabel (envsPG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ)
      (pubCFT δ V x ρ χ) Q ⟨0, V.hN⟩)).2.2.1.s
    rw [hP, hs']; exact b1
  · show SemanticStrategy.bindFP _ _ (rowLabel (envsPG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ)
      (pubCFT δ V x ρ χ) Q ⟨0, V.hN⟩)).2.2.1.f
    rw [hP, hf']; exact b2
  · show SemanticStrategy.bindFP _ _ (rowLabel (envsPG (towerGather δ V.basis) V (chalVQ7T δ V.basis χ)
      (pubCFT δ V x ρ χ) Q ⟨0, V.hN⟩)).2.2.1.e
    rw [hP, he']; exact b3

end Fam


/-! ## 8. `compSoundnessVCLT`: moved to `TowerCompFamilyT.lean` with the honest fields. -/


/-! ## 9. Round placement of the Im FP columns (GEN-C4's unconfirmed item) -/

/-- **The Im twins of the fingerprint roles are co-staged with the Re columns.**  For every fingerprint
role `r`, each physical Im column (`c + k - 95`, `c = towerM.ext r`, source layout) of `tableVCLT` is
round `1`, the round of the Re columns `13 + 3r + k` at the 309 schedule (`fpCol_round_one`).  The
seed coins `χ2, χ3` that those `𝕂′`-valued fingerprints depend on are round-`0` coins
(`seed_coins_round_zero`), so a round-`1` column may read them: the Im twin reads nothing that the Re
column may not.  (This is the placement-level fact; that the protocol commits Re and Im of one
fingerprint together is the CF-T specification, not derived here.) -/
theorem imFP_costaged (hC : ℕ) :
    ∀ r : Fin 63, (r : ℕ) ∈ fpRoleList → ∀ c, towerM.ext r = some c → ∀ k < 3,
      ∃ hw : c + k - 95 < (tableVCLT hC).width,
        (tableVCLT hC).colRound ⟨c + k - 95, hw⟩ = 1 ∧
          RepartitionedStaging.newComputeColRound (13 + 3 * (r : ℕ) + k) = 1 := by
  intro r hr c hc k hk
  have hrr : (r : ℕ) < 58 ∧ ¬ (32 ≤ (r : ℕ) ∧ (r : ℕ) ≤ 35) := by
    have h : ∀ r ∈ fpRoleList, r < 58 ∧ ¬ (32 ≤ r ∧ r ≤ 35) := by decide
    exact h _ hr
  have hge := towerM_ext_ge r c hc
  have hlt := towerM_ext_round r hrr.1 hrr.2 c hc
  have hw : c + k - 95 < (tableVCLT hC).width := by simp [tableVCLT, vclWidthT]; omega
  exact ⟨hw, tableVCLT_colRound_im hC _ (by omega) (by omega) hw, fpCol_round_one _ hr k hk⟩

/-- The seed coins are round-`0` coins of the frame (`seed_coins_round_zero`, via `seedSpecVCL`). -/
theorem seedSpecVCL_round_zero {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K]
    (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] :
    ∀ i ∈ (seedSpecVCL (algebraMap F K δ)).dep, frameVCL.sampledAfter i = 0 :=
  (seedSpecVCL (algebraMap F K δ)).round0


/-- **Negative control**: with a failed check (`¬ GoodCFT`: a bad adjacency / injectivity / `hchar` /
`N ≤ char` / `ρ 0 ≠ 0`), the tower CF chip accepts NO trace. -/
theorem chipCFT_rejects_bad {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [DecidableEq F] {hC : ℕ} {S : MemShape}
    (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (V : VerifierData F K hC S) (x : ℕ → F)
    (ρ : Fin 3 → Quad (algebraMap F K δ)) (χ : Coins frameVCL K) (Q : Fin (tableVCLT hC).width → F[X])
    (hng : ¬ GoodCFT δ V ρ) :
    ¬ RAP.SatisfiesWithPreprocessing (chipCFT δ V x ρ χ)
      (fun j => Q (Fin.cast (chipCFT_width δ V x ρ χ) j)) :=
  fun h => hng (chipCFT_good δ V x ρ χ Q h)

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54