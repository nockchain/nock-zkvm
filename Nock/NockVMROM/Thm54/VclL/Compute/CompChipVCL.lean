import Nock.NockVMROM.Thm54.VclL.Compute.NodeRecQ7
import Nock.NockVMROM.Thm54.VclL.Compute.ChipV

/-!
# CF-A : the compute family's chip, `reqFacts`, `reqRecords` and bounds at VCL

.

It places `ρ 1`, `ρ 2` at the export / path terminal publics
(`rhoExportPub` / `rhoPathPub`, `pubCF`); every other public is `pubVQ7`.

* `chipCF`, `chipCF_width`, `chipCF_good`, `chipCF_sat` — the chip and its acceptance;
* `reqFactsCF` — the three accumulators' `ReqIOFacts` at the IO coins `(χ4, χ5)`;
* `reqRecsCF` / `reqRecsQ7_chal_irrel` / `reqRecsQ7_round1` — the records are a function of the
  columns of round `≤ 1` alone (no coin, no public);
* `reqRecsQ7_length_*` — export `≤ 3N`, path `≤ N`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace CompChipVCL

open Nock Nock.Reified Nock.Framework Nock.Framework.Reify Module
open Nock.ComputeTable (State)
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7
open Nock.NockVMROM.Thm54.VclL.Compute.NodeRecQ7
open scoped Polynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 300000

noncomputable section

/-! ## 1. Records read round-`≤ 1` columns only -/

section recs
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- An entry reads only columns of round `≤ 1`. -/
def entryOk : Entry → Bool
  | .k l => (List.range 3).all fun j => decide (colRoundVCLE (l + j) ≤ 1)
  | .f c => decide (colRoundVCLE c ≤ 1)

theorem entryVal_congr (b : Basis (Fin 3) F K) (env env' : Env F)
    (hc : ∀ c, colRoundVCLE c ≤ 1 → env.trace c = env'.trace c) (e : Entry) (he : entryOk e = true) :
    e.val b env = e.val b env' := by
  cases e with
  | k l =>
    unfold Entry.val
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj := j.isLt
    simp only [entryOk, List.all_eq_true, List.mem_range, decide_eq_true_eq] at he
    rw [hc (l + j) (he j hj)]
  | f c =>
    simp only [entryOk, decide_eq_true_eq] at he
    exact congrArg _ (hc c he)

theorem recVal_congr (b : Basis (Fin 3) F K) (env env' : Env F)
    (hc : ∀ c, colRoundVCLE c ≤ 1 → env.trace c = env'.trace c) {m : ℕ} (r : Fin m → Entry)
    (hr : ∀ i, entryOk (r i) = true) : recVal b env r = recVal b env' r :=
  funext fun i => entryVal_congr b env env' hc _ (hr i)

theorem formulaRec_ok : ∀ i, entryOk (formulaRec i) = true := by decide +kernel
theorem tailRec_ok : ∀ i, entryOk (tailRec i) = true := by decide +kernel
theorem ttRec_ok : ∀ i, entryOk (ttRec i) = true := by decide +kernel
theorem op0PathRec_ok : ∀ i, entryOk (op0PathRec i) = true := by decide +kernel
theorem op9PathRec_ok : ∀ i, entryOk (op9PathRec i) = true := by decide +kernel

theorem sel_round_le1 (c : ℕ) (hc : c < 13) : colRoundVCLE c ≤ 1 := by
  rw [selCol_round0 c hc]; omega

theorem actX_congr (env env' : Env F)
    (hc : ∀ c, colRoundVCLE c ≤ 1 → env.trace c = env'.trace c) (s : ℕ) :
    actX (K := K) env s = actX (K := K) env' s := by
  rcases s with _ | _ | _ | s
  · rfl
  · simp only [actX, selSum_eval, slot1ExportSels, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    rw [hc 2 (sel_round_le1 _ (by norm_num)), hc 5 (sel_round_le1 _ (by norm_num)),
      hc 6 (sel_round_le1 _ (by norm_num)), hc 7 (sel_round_le1 _ (by norm_num)),
      hc 8 (sel_round_le1 _ (by norm_num)), hc 9 (sel_round_le1 _ (by norm_num))]
  · simp only [actX]; rw [hc 6 (sel_round_le1 _ (by norm_num))]
  · rfl

theorem actP_congr (env env' : Env F)
    (hc : ∀ c, colRoundVCLE c ≤ 1 → env.trace c = env'.trace c) (s : ℕ) :
    actP (K := K) env s = actP (K := K) env' s := by
  rcases s with _ | _ | s
  · simp only [actP]; rw [hc 0 (sel_round_le1 _ (by norm_num))]
  · simp only [actP]; rw [hc 9 (sel_round_le1 _ (by norm_num))]
  · rfl

theorem recX11_congr (b : Basis (Fin 3) F K) (env env' : Env F)
    (hc : ∀ c, colRoundVCLE c ≤ 1 → env.trace c = env'.trace c) (s : ℕ) :
    recX11 b env s = recX11 b env' s := by
  unfold recX11
  congr 1
  rcases s with _ | _ | s
  · exact recVal_congr b env env' hc _ formulaRec_ok
  · exact recVal_congr b env env' hc _ tailRec_ok
  · exact recVal_congr b env env' hc _ ttRec_ok

theorem recP_congr (b : Basis (Fin 3) F K) (env env' : Env F)
    (hc : ∀ c, colRoundVCLE c ≤ 1 → env.trace c = env'.trace c) (s : ℕ) :
    recP b env s = recP b env' s := by
  rcases s with _ | s
  · exact recVal_congr b env env' hc _ op0PathRec_ok
  · exact recVal_congr b env env' hc _ op9PathRec_ok

end recs

section recsEq
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq K] {hC : ℕ} {S : MemShape}

theorem rowEnvs_trace_round (V : VerifierData F K hC S) (c1 p1 c2 p2 : ℕ → F) (Q Q' : Fin 232 → F[X])
    (hQ : ∀ j : Fin 232, colRoundVCLE j ≤ 1 → Q j = Q' j) (i : ℕ) :
    ∀ c, colRoundVCLE c ≤ 1 →
      (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q c1 p1 i).trace c =
        (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q' c2 p2 i).trace c := by
  intro c hc
  simp only [rowEnvs]
  split_ifs <;> simp only [envOfTrace] <;> split_ifs with h
  all_goals first | rfl | rw [hQ ⟨c, h⟩ hc]

/-- **The committed request records read only columns of round `≤ 1`** (no coin, no public). -/
theorem reqRecsQ7_round1 (V : VerifierData F K hC S) (c1 p1 c2 p2 : ℕ → F) (Q Q' : Fin 232 → F[X])
    (hQ : ∀ j : Fin 232, colRoundVCLE j ≤ 1 → Q j = Q' j) (a : Fin 3) :
    reqRecsQ7 V c1 p1 Q a = reqRecsQ7 V c2 p2 Q' a := by
  have ht := rowEnvs_trace_round V c1 p1 c2 p2 Q Q' hQ
  fin_cases a
  · rfl
  · show exportRecsQ7 V c1 p1 Q = exportRecsQ7 V c2 p2 Q'
    unfold exportRecsQ7
    congr 1
    · funext i s
      split_ifs
      · exact actX_congr _ _ (ht i) s
      · rfl
    · funext i s
      exact recX11_congr _ _ _ (ht i) s
  · show pathRecsQ7 V c1 p1 Q = pathRecsQ7 V c2 p2 Q'
    unfold pathRecsQ7
    congr 1
    · funext i s
      split_ifs
      · exact actP_congr _ _ (ht i) s
      · rfl
    · funext i s
      exact recP_congr _ _ _ (ht i) s

end recsEq

/-! ## 2. The chip -/

section chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [CharP K (ringChar K)] [DecidableEq F] {hC : ℕ} {S : MemShape}

def GoodCF (V : VerifierData F K hC S) (ρ : Fin 3 → K) : Prop :=
  V.AdjacentC ∧ Function.Injective V.computeNodes ∧ (∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1) ∧
    V.N ≤ ringChar K ∧ ρ 0 = 0

/-- **The publics of the CF chip**: `ρ 1`, `ρ 2` at the export / path terminal limbs, `pubVQ7` elsewhere. -/
def pubCF (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → K) (χ : Coins frameVCL K) : ℕ → F :=
  fun j =>
    if h1 : rhoExportPub ≤ j ∧ j < rhoExportPub + 3 then
      coord V.basis (ρ 1) ⟨j - rhoExportPub, by omega⟩
    else if h2 : rhoPathPub ≤ j ∧ j < rhoPathPub + 3 then
      coord V.basis (ρ 2) ⟨j - rhoPathPub, by omega⟩
    else pubVQ7 V.basis V.claim x χ j

open Classical in
/-- **The CF chip**: the side chip `computeChipVCLQ7S` at the frame coin map when `GoodCF V ρ`, the
rejecting chip (`computeChipVCLF … false`) otherwise. -/
def chipCF (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → K) (χ : Coins frameVCL K) :
    FixedPreprocessingRAP F :=
  if GoodCF V ρ then
    computeChipVCLQ7S V.hN V.computeNodes V.basis 21 24 (chalVQ7 V.basis χ) (pubCF V x ρ χ) V.orbitC
  else
    computeChipVCLF V.hN V.computeNodes V.basis 21 24 false (chalVQ7 V.basis χ) (pubCF V x ρ χ)
      V.orbitC

theorem chipCF_width (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → K) (χ : Coins frameVCL K) :
    (chipCF V x ρ χ).rap.w = 232 := by
  unfold chipCF; split_ifs <;> rfl

theorem chipCF_good (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → K) (χ : Coins frameVCL K)
    (Q : Fin 232 → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (chipCF V x ρ χ) (fun j => Q (Fin.cast (chipCF_width V x ρ χ) j))) :
    GoodCF V ρ := by
  by_contra hng
  have hc : chipCF V x ρ χ = computeChipVCLF V.hN V.computeNodes V.basis 21 24 false
      (chalVQ7 V.basis χ) (pubCF V x ρ χ) V.orbitC := by
    unfold chipCF; exact if_neg hng
  have key : ∀ c : FixedPreprocessingRAP F, c = computeChipVCLF V.hN V.computeNodes V.basis 21 24 false
      (chalVQ7 V.basis χ) (pubCF V x ρ χ) V.orbitC → ∀ P : Fin c.rap.w → F[X],
      RAP.SatisfiesWithPreprocessing c P → False := by
    intro c hc P hP
    subst hc
    exact Bool.false_ne_true (sat_ok V.hN V.computeNodes V.basis 21 24 false _ _ V.orbitC P hP)
  exact key _ hc _ hP

theorem chipCF_sat (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → K) (χ : Coins frameVCL K)
    (Q : Fin 232 → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (chipCF V x ρ χ) (fun j => Q (Fin.cast (chipCF_width V x ρ χ) j))) :
    RAP.SatisfiesWithPreprocessing
      (computeChipVCLQ7S V.hN V.computeNodes V.basis 21 24 (chalVQ7 V.basis χ) (pubCF V x ρ χ) V.orbitC)
      Q := by
  have hg := chipCF_good V x ρ χ Q hP
  have hc : chipCF V x ρ χ = computeChipVCLQ7S V.hN V.computeNodes V.basis 21 24 (chalVQ7 V.basis χ)
      (pubCF V x ρ χ) V.orbitC := by
    unfold chipCF; exact if_pos hg
  have key : ∀ c : FixedPreprocessingRAP F, c = computeChipVCLQ7S V.hN V.computeNodes V.basis 21 24
      (chalVQ7 V.basis χ) (pubCF V x ρ χ) V.orbitC → ∀ hw : c.rap.w = 232,
      RAP.SatisfiesWithPreprocessing c (fun j => Q (Fin.cast hw j)) →
      RAP.SatisfiesWithPreprocessing (computeChipVCLQ7S V.hN V.computeNodes V.basis 21 24
        (chalVQ7 V.basis χ) (pubCF V x ρ χ) V.orbitC) Q := by
    intro c hc hw hP
    subst hc
    have hfun : (fun j => Q (Fin.cast hw j)) = Q := funext fun j => rfl
    rw [hfun] at hP
    exact hP
  exact key _ hc _ hP

end chip

/-! ## 3. `reqFacts` at the IO coins `(χ4, χ5)` -/

/-- The CF's IO coins: slots `4`, `5` of `frameVCL`, in `𝕂`. -/
def ioCF (K : Type) : IOCoinSpec frameVCL K K :=
  IOCoinSpec.ofPair frameVCL K ⟨4, by decide⟩ ⟨5, by decide⟩

/-- Transport of a consumer fact along equal denominators and terminals. -/
def castReq {Kio : Type} [Field Kio] {m : ℕ} {den den' : (Fin m → Kio) → Kio} {ρ ρ' : Kio}
    (F0 : ReqIOFacts den ρ) (hd : den = den') (hρ : ρ = ρ') : ReqIOFacts den' ρ' := by
  subst hd; subst hρ; exact F0

theorem castReq_records {Kio : Type} [Field Kio] {m : ℕ} {den den' : (Fin m → Kio) → Kio} {ρ ρ' : Kio}
    (F0 : ReqIOFacts den ρ) (hd : den = den') (hρ : ρ = ρ') : (castReq F0 hd hρ).records = F0.records := by
  subst hd; subst hρ; rfl

section reqf
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [CharP K (ringChar K)] [DecidableEq F] {hC : ℕ} {S : MemShape}

theorem limbVal_pubCF_export (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → K)
    (χ : Coins frameVCL K) : limbVal V.basis (pubCF V x ρ χ) rhoExportPub = ρ 1 := by
  unfold limbVal
  have hc : ∀ k : Fin 3, pubCF V x ρ χ (rhoExportPub + (k : ℕ)) = coord V.basis (ρ 1) k := by
    intro k
    have hk := k.isLt
    unfold pubCF
    rw [dif_pos ⟨by omega, by omega⟩]
    exact congrArg _ (Fin.ext (by simp))
  simp_rw [hc]
  exact reconstruct_coord V.basis _

theorem limbVal_pubCF_path (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → K)
    (χ : Coins frameVCL K) : limbVal V.basis (pubCF V x ρ χ) rhoPathPub = ρ 2 := by
  unfold limbVal
  have hc : ∀ k : Fin 3, pubCF V x ρ χ (rhoPathPub + (k : ℕ)) = coord V.basis (ρ 2) k := by
    intro k
    have hk := k.isLt
    unfold pubCF
    rw [dif_neg (by unfold rhoExportPub rhoPathPub; omega), dif_pos ⟨by omega, by omega⟩]
    exact congrArg _ (Fin.ext (by simp))
  simp_rw [hc]
  exact reconstruct_coord V.basis _

/-- **The CF's `reqFacts`**: validity `ρ 0 = 0` (no records); export / path from the accepted row
family, transported to the IO coins `(χ4, χ5)` and the terminals `ρ 1`, `ρ 2`. -/
def reqFactsCF (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → K) (χ : Coins frameVCL K)
    (Q : Fin 232 → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (chipCF V x ρ χ) (fun j => Q (Fin.cast (chipCF_width V x ρ χ) j))) :
    ∀ a : Fin 3, ReqIOFacts (FiniteIO.compress (m := RV.mVCL a) ((ioCF K).ioCoins χ)) (ρ a) :=
  have hg := chipCF_good V x ρ χ Q hP
  have hs := chipCF_sat V x ρ χ Q hP
  let A := acceptedRowsQ7S_of_sat V.hN V.computeNodes V.basis 21 24 (chalVQ7 V.basis χ)
    (pubCF V x ρ χ) V.orbitC Q hs hg.2.1 hg.1 hg.2.2.1
  fun a => match a with
  | ⟨0, _⟩ => ⟨[], by simp [hg.2.2.2.2], fun r hr => absurd hr (List.not_mem_nil)⟩
  | ⟨1, _⟩ => castReq (exportReqFactsQ7S V.basis 21 24 V.N V.N
      (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q (chalVQ7 V.basis χ) (pubCF V x ρ χ))
      (chalVQ7 V.basis χ) (pubCF V x ρ χ) A)
      (by rw [coinsV_chalVQ7]; rfl) (limbVal_pubCF_export V x ρ χ)
  | ⟨2, _⟩ => castReq (pathReqFactsQ7S V.basis 21 24 V.N V.N
      (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q (chalVQ7 V.basis χ) (pubCF V x ρ χ))
      (chalVQ7 V.basis χ) (pubCF V x ρ χ) A)
      (by rw [coinsV_chalVQ7]; rfl) (limbVal_pubCF_path V x ρ χ)

/-- **The CF's `reqRecords`**: the committed records, a function of the columns alone. -/
def reqRecordsCF (V : VerifierData F K hC S) (_x : ℕ → F) (Q : Fin 232 → F[X]) (_χ : Coins frameVCL K) :
    ∀ a : Fin 3, List (Fin (RV.mVCL a) → K) :=
  reqRecsQ7 V (fun _ => 0) (fun _ => 0) Q

theorem reqFactsCF_records (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → K) (χ : Coins frameVCL K)
    (Q : Fin 232 → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (chipCF V x ρ χ) (fun j => Q (Fin.cast (chipCF_width V x ρ χ) j)))
    (a : Fin 3) : (reqFactsCF V x ρ χ Q hP a).records = reqRecordsCF V x Q χ a := by
  fin_cases a
  · rfl
  · refine (castReq_records _ _ _).trans ?_
    exact reqRecsQ7_round1 V _ _ _ _ Q Q (fun _ _ => rfl) 1
  · refine (castReq_records _ _ _).trans ?_
    exact reqRecsQ7_round1 V _ _ _ _ Q Q (fun _ _ => rfl) 2

end reqf



/-! ## 4. The request bounds: export `≤ 3N`, path `≤ N` -/

theorem activeRecords_two_le {Kio : Type} [Field Kio] [DecidableEq Kio] {m : ℕ} (N : ℕ)
    (act : ℕ → ℕ → Kio) (rec : ℕ → ℕ → Fin m → Kio)
    (h : ∀ i, ¬ (act i 0 = 1 ∧ act i 1 = 1)) : (activeRecords N 2 act rec).length ≤ N := by
  unfold activeRecords
  rw [List.length_flatMap]
  calc ((List.range N).map fun i => ((List.range 2).filterMap fun s =>
          if act i s = 1 then some (rec i s) else none).length).sum
      ≤ ((List.range N).map fun _ => 1).sum := by
        apply List.sum_le_sum
        intro i _
        have h2 : List.range 2 = [0, 1] := rfl
        rw [h2]
        simp only [List.filterMap_cons, List.filterMap_nil]
        have := h i
        split_ifs <;> simp_all
    _ = N := by simp

section bounds
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [CharP K (ringChar K)] [DecidableEq F] {hC : ℕ} {S : MemShape}

/-- **The CF's `reqBound`**: validity `0`, export `3N`, path `N`. -/
def reqBoundCF (V : VerifierData F K hC S) : Fin 3 → ℕ := ![0, 3 * V.N, V.N]

theorem actP_excl (env : Env F) (st : State) (h : SelAt env st) :
    ¬ (actP (K := K) env 0 = 1 ∧ actP (K := K) env 1 = 1) := by
  rintro ⟨h0, h1⟩
  have ht := selAt_trace h
  simp only [actP] at h0 h1
  have e0 : env.trace 0 = 1 := (algebraMap F K).injective (by rw [h0, map_one])
  have e1 : env.trace 9 = 1 := (algebraMap F K).injective (by rw [h1, map_one])
  rw [ht 0 (by norm_num)] at e0
  rw [ht 9 (by norm_num)] at e1
  cases st <;> simp [selIdx] at e0 e1

theorem reqRecsQ7_length_le (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X])
    (hsel : ∀ i < V.N, ∃ st, SelAt (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) st)
    (a : Fin 3) : (reqRecsQ7 V chalV pubVal Q a).length ≤ reqBoundCF V a := by
  fin_cases a
  · show ([] : List (Fin 5 → K)).length ≤ 0
    simp
  · show (exportRecsQ7 V chalV pubVal Q).length ≤ 3 * V.N
    have := activeRecords_length_le (Kio := K) V.N 3
      (fun i s => if i < V.N then
        actX (K := K) (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s else 0)
      (fun i s => recX11 V.basis (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s)
    unfold exportRecsQ7
    omega
  · show (pathRecsQ7 V chalV pubVal Q).length ≤ V.N
    unfold pathRecsQ7
    refine activeRecords_two_le V.N _ _ fun i => ?_
    by_cases hi : i < V.N
    · obtain ⟨st, hst⟩ := hsel i hi
      simp only [hi, if_true]
      exact actP_excl _ st hst
    · simp [hi]

theorem reqFactsCF_length (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → K) (χ : Coins frameVCL K)
    (Q : Fin 232 → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (chipCF V x ρ χ) (fun j => Q (Fin.cast (chipCF_width V x ρ χ) j)))
    (a : Fin 3) : (reqFactsCF V x ρ χ Q hP a).records.length ≤ reqBoundCF V a := by
  rw [reqFactsCF_records]
  have hg := chipCF_good V x ρ χ Q hP
  have hs := chipCF_sat V x ρ χ Q hP
  have A := acceptedRowsQ7S_of_sat V.hN V.computeNodes V.basis 21 24 (chalVQ7 V.basis χ)
    (pubCF V x ρ χ) V.orbitC Q hs hg.2.1 hg.1 hg.2.2.1
  have h1 := reqRecsQ7_length_le V (chalVQ7 V.basis χ) (pubCF V x ρ χ) Q (fun i hi => A.sel i hi) a
  have h2 := reqRecsQ7_round1 V (chalVQ7 V.basis χ) (pubCF V x ρ χ) (fun _ => 0) (fun _ => 0) Q Q
    (fun _ _ => rfl) a
  unfold reqRecordsCF
  rw [← h2]
  exact h1

end bounds

end

end CompChipVCL
end VclL.Compute
end Nock.NockVMROM.Thm54
