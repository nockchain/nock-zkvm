import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestT
import Nock.NockVMROM.Thm54.VclL.Compute.TowerRowTerms

/-!

This module proves:

* `vclFill_nonacc` / `rnd_acc`: the VCL fill off the four accumulator triples does not depend on the
  accumulators, and the accumulator columns are round `2` (no record reads them);
* `den_agree_rnd`: `den₀′ / den₁′ / den₂′` read only round-`≤ 1` columns, the selectors and the coins;
* `envAcc_agree_offAcc`: the trace with the accumulators filled and the trace with them zeroed agree at
  every column off the accumulators (the slot inverses `den′⁻¹` agree too: `inv_agree_acc`);
* `termQ_acc_eq`: the per-row terms at the final env equal those at the accumulator-zeroed env;
* `accGatesT_T_of_terms`: all 36 accumulator gates hold at EVERY row of the honest trace, given only the
  two terminal identities `Σ_j termQ(envAcc … 0 0 j) = reqT t χ 1 / 2` (no bad-set hypothesis needed).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Walk Nock.ComputeTable Nock.Reified Module
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0TowerFP

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

/-! ## 1. The accumulator columns -/

/-- The VCL columns holding the two accumulators, Re (`226..231`) and Im (`403..408`). -/
def accColT (c : ℕ) : Prop := (226 ≤ c ∧ c < 232) ∨ (403 ≤ c ∧ c < 409)

instance (c : ℕ) : Decidable (accColT c) := by unfold accColT; infer_instance

/-- **The accumulator columns are round `2`**: no round-`≤ 1` column is an accumulator column. -/
theorem rnd_acc (c : ℕ) (hc : rnd c ≤ 1) : ¬ accColT c := by
  intro ha
  rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have key : ∀ j : Fin 6, colRoundVCLE (226 + j.1) = 2 := by decide +kernel
    have := key ⟨c - 226, by omega⟩
    simp only [show 226 + (c - 226) = c by omega] at this
    simp only [rnd, h2, if_true, this] at hc
    omega
  · simp only [rnd, show ¬ c < 232 by omega, show ¬ c < 388 by omega, show c ≠ z1Col by
      simp only [z1Col]; omega, if_false] at hc
    omega

/-- The selector columns `0..10` are round `≤ 1`. -/
theorem rnd_sel : ∀ c, c < 11 → rnd c ≤ 1 := by
  have key : ∀ j : Fin 11, rnd j.1 ≤ 1 := by decide +kernel
  intro c hc
  exact key ⟨c, hc⟩

section Fill
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- Off the accumulator columns the VCL fill does not depend on the accumulators. -/
theorem vclFill_nonacc (b : Basis (Fin 3) F K) (ser : F) (ax : ℕ) (fIdx vI0 vI1 : F)
    (inv0 inv1 inv2 accX accP : Quad (algebraMap F K δ)) (c : ℕ) (hc : ¬ accColT c) :
    vclFill (δ := δ) b ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP c =
      vclFill (δ := δ) b ser ax fIdx vI0 vI1 inv0 inv1 inv2 0 0 c := by
  unfold accColT at hc
  have h1 : ¬ (accExportBase ≤ c ∧ c < accExportBase + 3) := by simp only [accExportBase]; omega
  have h2 : ¬ (accPathBase ≤ c ∧ c < accPathBase + 3) := by simp only [accPathBase]; omega
  have h3 : ¬ (accImExport ≤ c ∧ c < accImExport + 3) := by simp only [accImExport]; omega
  have h4 : ¬ (accImPath ≤ c ∧ c < accImPath + 3) := by simp only [accImPath]; omega
  unfold vclFill
  split_ifs <;> first
    | rfl
    | simp only [limbAt, h1, h2, h3, h4, dif_neg, not_false_eq_true]

theorem vclFill_accX (b : Basis (Fin 3) F K) ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP (k : Fin 3) :
    vclFill (δ := δ) b ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP (accExportBase + k) =
      coord b (Quad.re _ accX) k := by
  fin_cases k <;>
    simp [vclFill, limbAt, z1Col, inv0Base, lookupInvBase, accExportBase, accPathBase, invImBase, accImExport,
      accImPath, coord]

theorem vclFill_accXIm (b : Basis (Fin 3) F K) ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP (k : Fin 3) :
    vclFill (δ := δ) b ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP (accImExport + k) =
      coord b (Quad.im _ accX) k := by
  fin_cases k <;>
    simp [vclFill, limbAt, z1Col, inv0Base, lookupInvBase, accExportBase, accPathBase, invImBase, accImExport,
      accImPath, coord]

theorem vclFill_accP (b : Basis (Fin 3) F K) ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP (k : Fin 3) :
    vclFill (δ := δ) b ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP (accPathBase + k) =
      coord b (Quad.re _ accP) k := by
  fin_cases k <;>
    simp [vclFill, limbAt, z1Col, inv0Base, lookupInvBase, accExportBase, accPathBase, invImBase, accImExport,
      accImPath, coord]

theorem vclFill_accPIm (b : Basis (Fin 3) F K) ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP (k : Fin 3) :
    vclFill (δ := δ) b ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP (accImPath + k) =
      coord b (Quad.im _ accP) k := by
  fin_cases k <;>
    simp [vclFill, limbAt, z1Col, inv0Base, lookupInvBase, accExportBase, accPathBase, invImBase, accImExport,
      accImPath, coord]

/-- **`den₀′ / den₁′ / den₂′` read only round-`≤ 1` columns** (and the coins). -/
theorem den_agree_rnd (b : Basis (Fin 3) F K) (E E' : Env F)
    (hE : ∀ c, rnd c ≤ 1 → E.trace c = E'.trace c) (hch : E.chal = E'.chal) :
    den0Q δ (gatherEnv b E) E = den0Q δ (gatherEnv b E') E' ∧
      den1Q δ (gatherEnv b E) E = den1Q δ (gatherEnv b E') E' ∧
      den2Q δ (gatherEnv b E) E = den2Q δ (gatherEnv b E') E' := by
  have hcoins : coinsQ δ (gatherEnv b E) E = coinsQ δ (gatherEnv b E') E' := by
    simp only [coinsQ, qγ, qρ, qvar_val, kread, gatherEnv, hch]
  have hsel : ∀ l : List ℕ, (∀ j ∈ l, j < 11) →
      Q.val δ (qlift F (selSum l)) (gatherEnv b E) E = Q.val δ (qlift F (selSum l)) (gatherEnv b E') E' := by
    intro l hl
    rw [qlift_val, qlift_val, selSum_eval_congr E E' l (fun j hj => hE j (rnd_sel j (hl j hj)))]
  have hsv : ∀ j, j < 11 → Q.val δ (qlift F (selVar j)) (gatherEnv b E) E =
      Q.val δ (qlift F (selVar j)) (gatherEnv b E') E' := by
    intro j hj
    rw [qlift_val, qlift_val]
    simp only [selVar, CoeffExpr.eval]
    rw [hE j (rnd_sel j hj)]
  refine ⟨?_, ?_, ?_⟩
  · unfold den0Q
    rw [hcoins]
    congr 1
    funext c
    exact recQ0_val_agree δ b E E' hE c
  · unfold den1Q
    rw [hsv 0 (by norm_num), hsel slot1ExportSels (by decide), hcoins,
      recValQ_agree δ b E E' hE _ op0PathRec_R1, recValQ_agree δ b E E' hE _ tailRec_R1]
  · unfold den2Q
    rw [hsv 6 (by norm_num), hsv 9 (by norm_num), hcoins,
      recValQ_agree δ b E E' hE _ ttRec_R1, recValQ_agree δ b E E' hE _ op9PathRec_R1]

/-- The per-row term `Σ_s act_s • inv_s` reads only the selectors and the slot inverse limbs. -/
theorem termVal_congr (b : Basis (Fin 3) F K) (slots : List (Slot F)) (E E' : Env F)
    (h : ∀ s ∈ slots, s.act.eval E = s.act.eval E' ∧ ∀ k, k < 3 → E.trace (s.invBase + k) = E'.trace (s.invBase + k)) :
    termVal b slots E = termVal b slots E' := by
  unfold termVal
  congr 1
  refine List.map_congr_left fun s hs => ?_
  rw [(h s hs).1, limbVal_congr b _ _ _ (h s hs).2]

/-- **The four accumulator slot lists read no accumulator column.** -/
theorem termQ_congr_offAcc (b : Basis (Fin 3) F K) (E E' : Env F)
    (hE : ∀ c, ¬ accColT c → E.trace c = E'.trace c) :
    termQ δ b accSlotsX accSlotsXIm E = termQ δ b accSlotsX accSlotsXIm E' ∧
      termQ δ b accSlotsPT accSlotsPImT E = termQ δ b accSlotsPT accSlotsPImT E' := by
  have hs : ∀ j, j < 11 → E.trace j = E'.trace j := fun j hj => hE j (by unfold accColT; omega)
  have hz1 : E.trace z1Col = E'.trace z1Col := hE z1Col (by unfold accColT z1Col; omega)
  have hA0 : (actP0 F).eval E = (actP0 F).eval E' := by
    simp only [actP0, notZ1, selVar, CoeffExpr.eval]; rw [hs 0 (by norm_num), hz1]
  have hA9 : (actP9 F).eval E = (actP9 F).eval E' := by
    simp only [actP9, notZ1, selVar, CoeffExpr.eval]; rw [hs 9 (by norm_num), hz1]
  have hsS : ∀ l : List ℕ, (∀ j ∈ l, j < 11) → (selSum l : CoeffExpr F).eval E = (selSum l).eval E' :=
    fun l hl => selSum_eval_congr E E' l fun j hj => hs j (hl j hj)
  have hsV : ∀ j, j < 11 → (selVar j : CoeffExpr F).eval E = (selVar j).eval E' := by
    intro j hj; simp only [selVar, CoeffExpr.eval]; exact hs j hj
  have hinv : ∀ base, (base = inv0Base ∨ base = lookupInvBase 0 ∨ base = lookupInvBase 1 ∨
      base = invImBase 0 ∨ base = invImBase 1 ∨ base = invImBase 2) →
      ∀ k, k < 3 → E.trace (base + k) = E'.trace (base + k) := by
    intro base hb k hk
    apply hE
    unfold accColT
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [inv0Base, lookupInvBase, invImBase] <;> omega
  unfold termQ
  refine ⟨?_, ?_⟩
  · rw [termVal_congr b accSlotsX E E' ?_, termVal_congr b accSlotsXIm E E' ?_]
    · intro s hm
      simp only [accSlotsXIm, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · exact ⟨rfl, hinv _ (by simp)⟩
      · exact ⟨hsS slot1ExportSels (by decide), hinv _ (by simp)⟩
      · exact ⟨hsV 6 (by norm_num), hinv _ (by simp)⟩
    · intro s hm
      simp only [accSlotsX, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · exact ⟨rfl, hinv _ (by simp)⟩
      · exact ⟨hsS slot1ExportSels (by decide), hinv _ (by simp)⟩
      · exact ⟨hsV 6 (by norm_num), hinv _ (by simp)⟩
  · rw [termVal_congr b accSlotsPT E E' ?_, termVal_congr b accSlotsPImT E E' ?_]
    · intro s hm
      simp only [accSlotsPImT, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact ⟨hA0, hinv _ (by simp)⟩
      · exact ⟨hA9, hinv _ (by simp)⟩
    · intro s hm
      simp only [accSlotsPT, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact ⟨hA0, hinv _ (by simp)⟩
      · exact ⟨hA9, hinv _ (by simp)⟩

end Fill

/-! ## 2. The filled and the accumulator-zeroed traces agree off the accumulators -/

section Agree
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]
variable (b : Basis (Fin 3) F K) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ))
  (D : HonestWalk (Quad (algebraMap F K δ))) (n : ℕ)
  (decAt : ℕ → Dec (Quad (algebraMap F K δ)))
  (ser : ℕ → F) (ax : ℕ → ℕ) (fIdx vI0 vI1 : ℕ → F) (accX accP : ℕ → Quad (algebraMap F K δ))
  (nodes : Fin n → F) (ω : F) (cv pv : ℕ → F)

/-- The auxiliary (zero-inverse) rows agree off the accumulators. -/
theorem vclColT_rows0_offAcc (c : ℕ) (hc : ¬ accColT c) :
    vclColT b (rows0 b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω) c =
      vclColT b (rows0 b χ αs D n decAt ser ax fIdx vI0 vI1 (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => (0 : Quad (algebraMap F K δ))) nodes ω) c := by
  funext i
  unfold vclColT
  split_ifs
  · simp only [rows0]
    rw [rowFinal_vcl χ αs D n decAt _ (vcl0 b ser ax fIdx vI0 vI1 (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => (0 : Quad (algebraMap F K δ)))), srcColT_vcl_irrel]
  · simp only [rows0]
    rw [rowFinal_vcl χ αs D n decAt _ (vcl0 b ser ax fIdx vI0 vI1 (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => (0 : Quad (algebraMap F K δ)))), srcColT_vcl_irrel]
  · show vcl0 b ser ax fIdx vI0 vI1 accX accP i c = vcl0 b ser ax fIdx vI0 vI1 (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => (0 : Quad (algebraMap F K δ))) i c
    simp only [vcl0]
    rw [vclFill_nonacc b _ _ _ _ _ _ _ _ _ _ c hc, vclFill_nonacc b _ _ _ _ _ _ _ _ _ _ c hc]

theorem env0_offAcc (j : Fin n) (c : ℕ) (hc : ¬ accColT c) :
    (env0 b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv j).trace c =
      (env0 b χ αs D n decAt ser ax fIdx vI0 vI1 (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => (0 : Quad (algebraMap F K δ))) nodes ω cv pv j).trace c := by
  simp only [env0, Reify.envOfTrace]
  split_ifs with hw
  · rw [honestQT_congr b nodes _ _ vclWidthT ⟨c, hw⟩ (vclColT_rows0_offAcc b χ αs D n decAt ser ax fIdx vI0 vI1
      accX accP nodes ω c hc)]
  · rfl

theorem envOfTrace_chal_rfl_aux {w w' : ℕ} (P : Fin w → Polynomial F) (P' : Fin w' → Polynomial F)
    (ω x x' : F) (cv pv : ℕ → F) :
    (Reify.envOfTrace P ω x cv pv).chal = (Reify.envOfTrace P' ω x' cv pv).chal := rfl

/-- **The slot inverses do not depend on the accumulators.** -/
theorem inv_agree_acc (j : ℕ) :
    inv0F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv j =
        inv0F b χ αs D n decAt ser ax fIdx vI0 vI1 (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => (0 : Quad (algebraMap F K δ))) nodes ω cv pv j ∧
      inv1F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv j =
        inv1F b χ αs D n decAt ser ax fIdx vI0 vI1 (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => (0 : Quad (algebraMap F K δ))) nodes ω cv pv j ∧
      inv2F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv j =
        inv2F b χ αs D n decAt ser ax fIdx vI0 vI1 (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => (0 : Quad (algebraMap F K δ))) nodes ω cv pv j := by
  by_cases h : j < n
  · obtain ⟨d0, d1, d2⟩ := den_agree_rnd (δ := δ) b
      (env0 b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv ⟨j, h⟩)
      (env0 b χ αs D n decAt ser ax fIdx vI0 vI1 (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => (0 : Quad (algebraMap F K δ))) nodes ω cv pv ⟨j, h⟩)
      (fun c hc => env0_offAcc b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv ⟨j, h⟩ c
        (rnd_acc c hc)) (envOfTrace_chal_rfl_aux _ _ _ _ _ _ _)
    simp only [inv0F, inv1F, inv2F, dif_pos h]
    exact ⟨by rw [d0], by rw [d1], by rw [d2]⟩
  · simp only [inv0F, inv1F, inv2F, dif_neg h, and_self]

/-- The final rows agree off the accumulators. -/
theorem vclColT_rowsFinal_offAcc (c : ℕ) (hc : ¬ accColT c) :
    vclColT b (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) c =
      vclColT b (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => (0 : Quad (algebraMap F K δ))) nodes ω cv pv) c := by
  funext i
  unfold vclColT
  split_ifs
  · simp only [rowsFinal]
    rw [rowFinal_vcl χ αs D n decAt _
      (vclFinal b χ αs D n decAt ser ax fIdx vI0 vI1 (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => (0 : Quad (algebraMap F K δ))) nodes ω cv pv), srcColT_vcl_irrel]
  · simp only [rowsFinal]
    rw [rowFinal_vcl χ αs D n decAt _
      (vclFinal b χ αs D n decAt ser ax fIdx vI0 vI1 (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => (0 : Quad (algebraMap F K δ))) nodes ω cv pv), srcColT_vcl_irrel]
  · show vclFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv i c =
      vclFinal b χ αs D n decAt ser ax fIdx vI0 vI1 (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => (0 : Quad (algebraMap F K δ))) nodes ω cv pv i c
    obtain ⟨e0, e1, e2⟩ := inv_agree_acc b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv i
    simp only [vclFinal]
    rw [e0, e1, e2, vclFill_nonacc b _ _ _ _ _ _ _ _ _ _ c hc, vclFill_nonacc b _ _ _ _ _ _ _ _ _ _ c hc]

end Agree

/-! ## 3. The accumulator gates at the honest trace -/

section Gates
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [DecidableEq F] {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))] {hC : ℕ} {S : MemShape}
variable (V : VerifierData F K hC S) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ)) {fuel : ℕ}
  {subject formula : Noun} {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))} {result : Noun}
  (hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel subject formula = .ok (t, result))

/-- The honest row environments (filled accumulators), as a function of the row index. -/
abbrev envsT : ℕ → Env F := envAcc V χ αs hgen (accXT V χ αs hgen) (accPT V χ αs hgen)

theorem envsT_eq (i : Fin V.N) : envsT V χ αs hgen i = envT V χ αs hgen i := by
  simp only [envsT, envAcc, dif_pos i.isLt]
  rfl

/-- **The per-row terms at the final env equal those at the accumulator-zeroed env.** -/
theorem termQ_acc_eq (j : ℕ) :
    termQ δ V.basis accSlotsX accSlotsXIm (envsT V χ αs hgen j) =
        termQ δ V.basis accSlotsX accSlotsXIm (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j) ∧
      termQ δ V.basis accSlotsPT accSlotsPImT (envsT V χ αs hgen j) =
        termQ δ V.basis accSlotsPT accSlotsPImT (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j) := by
  apply termQ_congr_offAcc
  intro c hc
  simp only [envsT, envAcc]
  split_ifs with hj
  · simp only [Reify.envOfTrace]
    split_ifs with hw
    · simp only [rowsAcc]
      rw [honestQT_congr V.basis V.computeNodes _ _ vclWidthT ⟨c, hw⟩
        (vclColT_rowsFinal_offAcc V.basis χ αs _ V.N _ _ _ _ _ _ _ _ V.computeNodes V.orbitC.ω _ _ c hc)]
    · rfl
  · rfl

/-- The sum of the Re (resp. Im) halves of the per-row terms. -/
theorem sum_termQ_re (slotsRe slotsIm : List (Slot F)) (E : ℕ → Env F) (m : ℕ) :
    Quad.re _ (∑ j ∈ Finset.range m, termQ δ V.basis slotsRe slotsIm (E j)) =
      ∑ j ∈ Finset.range m, termVal V.basis slotsRe (E j) := by
  unfold termQ; rw [sum_mk, Quad.re_mk]

theorem sum_termQ_im (slotsRe slotsIm : List (Slot F)) (E : ℕ → Env F) (m : ℕ) :
    Quad.im _ (∑ j ∈ Finset.range m, termQ δ V.basis slotsRe slotsIm (E j)) =
      ∑ j ∈ Finset.range m, termVal V.basis slotsIm (E j) := by
  unfold termQ; rw [sum_mk, Quad.im_mk]

/-- The accumulator prefix of `accXT` read through the final envs. -/
theorem accXT_eq (i : ℕ) :
    accXT V χ αs hgen i = ∑ j ∈ Finset.range i, termQ δ V.basis accSlotsX accSlotsXIm (envsT V χ αs hgen j) :=
  Finset.sum_congr rfl fun j _ => ((termQ_acc_eq V χ αs hgen j).1).symm

theorem accPT_eq (i : ℕ) :
    accPT V χ αs hgen i = ∑ j ∈ Finset.range i, termQ δ V.basis accSlotsPT accSlotsPImT (envsT V χ αs hgen j) :=
  Finset.sum_congr rfl fun j _ => ((termQ_acc_eq V χ αs hgen j).2).symm

variable (hnodes : ∀ i : Fin V.N, V.computeNodes i = V.orbitC.ω ^ (i : ℕ)) (hsize : V.N ≤ 2 ^ hC)

include hnodes hsize in
/-- The trace of the honest env at row `i`, column `c < 409`, is the row's value. -/
theorem envsT_trace (i : Fin V.N) {c : ℕ} (hc : c < vclWidthT) :
    (envsT V χ αs hgen i).trace c = vclColT V.basis (rowsT V χ αs hgen) c i := by
  rw [envsT_eq]
  exact env_honestQT_trace V.basis V.computeNodes (injective_of_pow V hnodes hsize) _ _ _ _ i hc

include hnodes hsize in
theorem envsT_next (i : Fin V.N) (hi : (i : ℕ) + 1 < V.N) {c : ℕ} (hc : c < vclWidthT) :
    (envsT V χ αs hgen i).traceNext c = vclColT V.basis (rowsT V χ αs hgen) c ⟨(i : ℕ) + 1, hi⟩ := by
  rw [envsT_eq]
  simp only [envT, traceT, Reify.envOfTrace]
  have hn : V.orbitC.ω * V.computeNodes i = V.computeNodes ⟨(i : ℕ) + 1, hi⟩ := by
    rw [hnodes, hnodes]; simp only; rw [pow_succ']
  rw [hn, dif_pos (show c < (tableVCLT hC).width from hc)]
  exact honestQT_eval (δ := δ) V.basis V.computeNodes (injective_of_pow V hnodes hsize) _ ⟨c, hc⟩ _

theorem rowsT_vclAt (i : Fin V.N) (c : ℕ) :
    (rowsT V χ αs hgen i).vcl c =
      vclFill (δ := δ) V.basis (serT i) (axT t i) (fIdxT t i) (vIT t 1 i) (vIT t 2 i)
        (inv0F V.basis χ αs (walkT χ αs hgen) V.N (decT χ αs t) serT (axT t) (fIdxT t) (vIT t 1) (vIT t 2)
          (accXT V χ αs hgen) (accPT V χ αs hgen) V.computeNodes V.orbitC.ω (chalVQ7T δ V.basis χ)
          (pubCFT δ V (xT t) (reqT t χ) χ) i)
        (inv1F V.basis χ αs (walkT χ αs hgen) V.N (decT χ αs t) serT (axT t) (fIdxT t) (vIT t 1) (vIT t 2)
          (accXT V χ αs hgen) (accPT V χ αs hgen) V.computeNodes V.orbitC.ω (chalVQ7T δ V.basis χ)
          (pubCFT δ V (xT t) (reqT t χ) χ) i)
        (inv2F V.basis χ αs (walkT χ αs hgen) V.N (decT χ αs t) serT (axT t) (fIdxT t) (vIT t 1) (vIT t 2)
          (accXT V χ αs hgen) (accPT V χ αs hgen) V.computeNodes V.orbitC.ω (chalVQ7T δ V.basis χ)
          (pubCFT δ V (xT t) (reqT t χ) χ) i)
        (accXT V χ αs hgen i) (accPT V χ αs hgen i) c := rfl

/-- The accumulator columns `226..231`, `403..408` of row `i` of `vclColT` are the VCL fill's. -/
theorem vclColT_acc (rows : Fin V.N → TowerRowVals (K := K) δ) (i : Fin V.N) (c : ℕ) (hc : accColT c) :
    vclColT V.basis rows c i = (rows i).vcl c := by
  unfold accColT at hc
  unfold vclColT
  rw [if_neg (by omega), if_neg (by omega)]

theorem pubCFT_rx (x : ℕ → F) (ρ : Fin 3 → Quad (algebraMap F K δ)) (k : Fin 3) :
    pubCFT δ V x ρ χ (rhoExportPub + k) = coord V.basis (Quad.re _ (ρ 1)) k := by
  have h : rhoExportPub ≤ rhoExportPub + (k : ℕ) ∧ rhoExportPub + (k : ℕ) < rhoExportPub + 3 := by omega
  simp only [pubCFT, dif_pos h]
  congr 1; ext; simp

theorem pubCFT_rxI (x : ℕ → F) (ρ : Fin 3 → Quad (algebraMap F K δ)) (k : Fin 3) :
    pubCFT δ V x ρ χ (rhoExportImPub + k) = coord V.basis (Quad.im _ (ρ 1)) k := by
  have h0 : ¬ (rhoExportPub ≤ rhoExportImPub + (k : ℕ) ∧ rhoExportImPub + (k : ℕ) < rhoExportPub + 3) := by
    simp only [rhoExportPub, rhoExportImPub]; omega
  have h : rhoExportImPub ≤ rhoExportImPub + (k : ℕ) ∧ rhoExportImPub + (k : ℕ) < rhoExportImPub + 3 := by omega
  simp only [pubCFT, dif_neg h0, dif_pos h]
  congr 1; ext; simp

theorem pubCFT_rp (x : ℕ → F) (ρ : Fin 3 → Quad (algebraMap F K δ)) (k : Fin 3) :
    pubCFT δ V x ρ χ (rhoPathPub + k) = coord V.basis (Quad.re _ (ρ 2)) k := by
  have h0 : ¬ (rhoExportPub ≤ rhoPathPub + (k : ℕ) ∧ rhoPathPub + (k : ℕ) < rhoExportPub + 3) := by
    simp only [rhoExportPub, rhoPathPub]; omega
  have h1 : ¬ (rhoExportImPub ≤ rhoPathPub + (k : ℕ) ∧ rhoPathPub + (k : ℕ) < rhoExportImPub + 3) := by
    simp only [rhoExportImPub, rhoPathPub]; omega
  have h : rhoPathPub ≤ rhoPathPub + (k : ℕ) ∧ rhoPathPub + (k : ℕ) < rhoPathPub + 3 := by omega
  simp only [pubCFT, dif_neg h0, dif_neg h1, dif_pos h]
  congr 1; ext; simp

theorem pubCFT_rpI (x : ℕ → F) (ρ : Fin 3 → Quad (algebraMap F K δ)) (k : Fin 3) :
    pubCFT δ V x ρ χ (rhoPathImPub + k) = coord V.basis (Quad.im _ (ρ 2)) k := by
  have h0 : ¬ (rhoExportPub ≤ rhoPathImPub + (k : ℕ) ∧ rhoPathImPub + (k : ℕ) < rhoExportPub + 3) := by
    simp only [rhoExportPub, rhoPathImPub]; omega
  have h1 : ¬ (rhoExportImPub ≤ rhoPathImPub + (k : ℕ) ∧ rhoPathImPub + (k : ℕ) < rhoExportImPub + 3) := by
    simp only [rhoExportImPub, rhoPathImPub]; omega
  have h2 : ¬ (rhoPathPub ≤ rhoPathImPub + (k : ℕ) ∧ rhoPathImPub + (k : ℕ) < rhoPathPub + 3) := by
    simp only [rhoPathPub, rhoPathImPub]; omega
  have h : rhoPathImPub ≤ rhoPathImPub + (k : ℕ) ∧ rhoPathImPub + (k : ℕ) < rhoPathImPub + 3 := by omega
  simp only [pubCFT, dif_neg h0, dif_neg h1, dif_neg h2, dif_pos h]
  congr 1; ext; simp

include hnodes hsize in
/-- **The accumulator gates at every row of the honest trace**, from the two terminal identities alone:
the prefix-sum fill satisfies the 36 gates of `accGatesT` at every row (`accGatesT_honest`), the terms at the
filled env being those at the accumulator-zeroed env (`termQ_acc_eq`). -/
theorem accGatesT_T_of_terms
    (hX : ∑ j ∈ Finset.range V.N, termQ δ V.basis accSlotsX accSlotsXIm
      (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j) = reqT t χ 1)
    (hP : ∑ j ∈ Finset.range V.N, termQ δ V.basis accSlotsPT accSlotsPImT
      (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j) = reqT t χ 2)
    (i : Fin V.N) : ∀ g ∈ (accGatesT : List (CoordinateCompiler.CoeffExpr F)), g.eval (envT V χ αs hgen i) = 0 := by
  rw [← envsT_eq]
  have hw : ∀ c, accColT c → c < vclWidthT := fun c hc => by unfold accColT at hc; simp only [vclWidthT]; omega
  have hacc : ∀ (i' : Fin V.N) (c : ℕ), accColT c → (envsT V χ αs hgen i').trace c = (rowsT V χ αs hgen i').vcl c :=
    fun i' c hc => by rw [envsT_trace V χ αs hgen hnodes hsize i' (hw c hc), vclColT_acc V _ i' c hc]
  have haccN : ∀ (hi : (i : ℕ) + 1 < V.N) (c : ℕ), accColT c →
      (envsT V χ αs hgen i).traceNext c = (rowsT V χ αs hgen ⟨(i : ℕ) + 1, hi⟩).vcl c :=
    fun hi c hc => by rw [envsT_next V χ αs hgen hnodes hsize i hi (hw c hc), vclColT_acc V _ _ c hc]
  have cX : ∀ k : Fin 3, accColT (accExportBase + k) := fun k => by
    unfold accColT accExportBase; have := k.isLt; omega
  have cXI : ∀ k : Fin 3, accColT (accImExport + k) := fun k => by
    unfold accColT accImExport; have := k.isLt; omega
  have cP : ∀ k : Fin 3, accColT (accPathBase + k) := fun k => by
    unfold accColT accPathBase; have := k.isLt; omega
  have cPI : ∀ k : Fin 3, accColT (accImPath + k) := fun k => by
    unfold accColT accImPath; have := k.isLt; omega
  have hb : ∀ c (hc : c < 13), (envsT V χ αs hgen i).trace c = (rowsT V χ αs hgen i).base ⟨c, hc⟩ := by
    intro c hc
    rw [envsT_trace V χ αs hgen hnodes hsize i (by simp only [vclWidthT]; omega)]
    simp only [vclColT, show c < 202 by omega, if_true, srcColT, hc, dif_pos]
  refine accGatesT_honest δ V.basis V.N i i.isLt (envsT V χ αs hgen) (reqT t χ 1) (reqT t χ 2)
    ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hb 11 (by norm_num), rowsT_base]; simp
  · rw [hb 12 (by norm_num), rowsT_base]; simp
  · rw [← hX]; exact Finset.sum_congr rfl fun j _ => (termQ_acc_eq V χ αs hgen j).1
  · rw [← hP]; exact Finset.sum_congr rfl fun j _ => (termQ_acc_eq V χ αs hgen j).2
  · intro k; rw [hacc i _ (cX k), rowsT_vclAt, vclFill_accX, accXT_eq, sum_termQ_re]
  · intro hi k; rw [haccN hi _ (cX k), rowsT_vclAt, vclFill_accX, accXT_eq, sum_termQ_re]
  · intro k; rw [hacc i _ (cXI k), rowsT_vclAt, vclFill_accXIm, accXT_eq, sum_termQ_im]
  · intro hi k; rw [haccN hi _ (cXI k), rowsT_vclAt, vclFill_accXIm, accXT_eq, sum_termQ_im]
  · intro k; rw [hacc i _ (cP k), rowsT_vclAt, vclFill_accP, accPT_eq, sum_termQ_re]
  · intro hi k; rw [haccN hi _ (cP k), rowsT_vclAt, vclFill_accP, accPT_eq, sum_termQ_re]
  · intro k; rw [hacc i _ (cPI k), rowsT_vclAt, vclFill_accPIm, accPT_eq, sum_termQ_im]
  · intro hi k; rw [haccN hi _ (cPI k), rowsT_vclAt, vclFill_accPIm, accPT_eq, sum_termQ_im]
  · intro k; simp only [envsT, envAcc, dif_pos i.isLt, Reify.envOfTrace]; exact pubCFT_rx V χ _ _ k
  · intro k; simp only [envsT, envAcc, dif_pos i.isLt, Reify.envOfTrace]; exact pubCFT_rxI V χ _ _ k
  · intro k; simp only [envsT, envAcc, dif_pos i.isLt, Reify.envOfTrace]; exact pubCFT_rp V χ _ _ k
  · intro k; simp only [envsT, envAcc, dif_pos i.isLt, Reify.envOfTrace]; exact pubCFT_rpI V χ _ _ k

end Gates

/-! ## 4. The terminals from the per-row record identities -/

section Rows
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [DecidableEq F] {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **The export terminal from the per-row identities** (`terminal_eq_closed`; one record per occurrence). -/
theorem sumX_of_rows {hC : ℕ} {S : MemShape} (V : VerifierData F K hC S) (χ : Coins frameVCL K)
    (αs : Quad (algebraMap F K δ)) {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))} {result : Noun}
    (hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel subject formula = .ok (t, result))
    (hN : V.N = nRows t)
    (hrow : ∀ j < V.N, termQ δ V.basis accSlotsX accSlotsXIm
        (envAcc V χ αs hgen (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => 0) j) =
      ((shallowSided (rowExportKeys (gRow t j))).map fun c =>
        (FiniteIO.compress (m := 11) ⟨γC (δF := δ) χ, ρC (δF := δ) χ⟩
          (xReq δ (zC (δF := δ) χ) (demT (F := F) (K := K) (δ := δ) t).cells c.1 c.2))⁻¹).sum) :
    ∑ j ∈ Finset.range V.N, termQ δ V.basis accSlotsX accSlotsXIm
        (envAcc V χ αs hgen (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => 0) j) = reqT t χ 1 := by
  rw [terminal_eq_closed V.N _ (γC χ) (ρC χ) (fun j => shallowSided (rowExportKeys (gRow t j)))
    (fun c => xReq δ (zC χ) (demT t).cells c.1 c.2) hrow (shallowSided (demT t).reads)]
  · rfl
  · show _ = shallowSided ((genRowsT t).flatMap rowExportKeys)
    rw [shallowSided_flatMap, flatMap_genRowsT, hN]

/-- **The path terminal from the per-row identities** (one provide request per occurrence; the path table's
`m = count` balances it, `HonestMemReq.lean::path_pTotal`). -/
theorem sumP_of_rows {hC : ℕ} {S : MemShape} (V : VerifierData F K hC S) (χ : Coins frameVCL K)
    (αs : Quad (algebraMap F K δ)) {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))} {result : Noun}
    (hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel subject formula = .ok (t, result))
    (hN : V.N = nRows t)
    (hrow : ∀ j < V.N, termQ δ V.basis accSlotsPT accSlotsPImT
        (envAcc V χ αs hgen (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => 0) j) =
      (((rowPathKeys (gRow t j)).filter fun r => isPathAx r.2).map fun r =>
        (FiniteIO.compress (m := 8) ⟨γC (δF := δ) χ, ρC (δF := δ) χ⟩
          (pReq δ (zC (δF := δ) χ) (demT (F := F) (K := K) (δ := δ) t).cells r))⁻¹).sum) :
    ∑ j ∈ Finset.range V.N, termQ δ V.basis accSlotsPT accSlotsPImT
        (envAcc V χ αs hgen (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => 0) j) = reqT t χ 2 := by
  rw [terminal_eq_closed V.N _ (γC χ) (ρC χ) (fun j => (rowPathKeys (gRow t j)).filter fun r => isPathAx r.2)
    (fun r => pReq δ (zC χ) (demT t).cells r) hrow ((demT t).preads.filter fun r => isPathAx r.2)]
  · rfl
  · show _ = ((genRowsT t).flatMap rowPathKeys).filter fun r => isPathAx r.2
    rw [pathFilter_flatMap, flatMap_genRowsT, hN]

/-- **`hacc` is a theorem**: the accumulator gates `accGatesT` hold at every row of the honest
trace — at EVERY coin vector, so a fortiori outside `badT` — from the per-row record identities
`hrowX_T` / `hrowP_T` (`TowerRowTerms.lean`).  Same statement as the deleted field. -/
theorem HonestVCLT.hacc {hC : ℕ} {S : MemShape} (H : HonestVCLT F K δ hC S) :
    ∀ (χ : Coins frameVCL K) (Qm : ∀ t : Fin S.k, Fin (S.table t).width → Polynomial F),
      (∀ s ∈ badT H.V H.t, ¬ s.mem (traceT H.V χ H.αs H.hgen, Qm) χ) →
      ∀ i : Fin H.V.N, ∀ g ∈ (accGatesT : List (CoordinateCompiler.CoeffExpr F)),
        g.eval (envT H.V χ H.αs H.hgen i) = 0 := by
  intro χ _ _ i
  exact accGatesT_T_of_terms H.V χ H.αs H.hgen H.hnodes H.hsize
    (sumX_of_rows H.V χ H.αs H.hgen H.hN (fun j hj => hrowX_T H.V H.αs H.hgen H.hnodes H.hsize H.hN χ j hj))
    (sumP_of_rows H.V χ H.αs H.hgen H.hN
      (fun j hj => hrowP_T H.V H.αs H.hgen H.hnodes H.hsize H.hN χ j hj)) i

end Rows

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
