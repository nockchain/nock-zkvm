/-
  Nock/NockVMROM/Thm54/VclL/Chips/StandaloneVCLW.lean

  **The end-to-end composition with the walk.**

  * `extraPremises_vclW`: the four `ExtraPremises` fields (twin of `extraPremises_vcl`).
  * `rowFactsAt_CFvW`: `rowFactsAt` at the compute family over `shapeVW` (the generic-`S` theorem).
  * **`vcl_standaloneW`**: `StandaloneThm54Statement CFvW MFvW (jointSummandsStd CFvW MFvW)`.
  * `epsilon_vclW_le` / `vcl_epsilonW_le`: `ε ≤ boundVCLW''` (walk rows `W` in place of `P`; walk event
    `15W/|𝕂|`; export total `3N + W + 2D`, path total `N + 2W`).
  * `vcl_standaloneW_soundness_le`, `vcl_standaloneW_155' / _154' / _164'` at VCL-L's budgets.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerCompFamilyT
import Nock.NockVMROM.Thm54.VclL.Compute.TowerRowFactsAt
import Nock.NockVMROM.Thm54.VclL.Chips.MemSoundnessVCLW
import Nock.NockVMROM.Thm54.P8Core.SVFrame.StandaloneGeneric
import Nock.NockVMROM.Thm54.VclL.Chips.Prelim
import Nock.NockVMROM.Thm54.VclL.Events.BoundW

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.StandaloneW

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Events
open Nock.NockVMROM.Thm54.FiniteIO

/-- The walk-path accumulator totals: validity `3D + 2`, export `3N + W + 2D`, path `N + 2W`. -/
def totVCLW (N D W : ℕ) : Fin 3 → ℕ := ![3 * D + 2, 3 * N + W + 2 * D, N + 2 * W]

section Eps
variable {F K Kio Kfp Key : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [Fintype F] [Field Kfp] [DecidableEq Key]
  [Fintype Kfp] [DecidableEq Kfp] [Field Kio] [Fintype Kio] [DecidableEq Kio] [Algebra F Kio]
  {hC hT hP wT wP : ℕ} {rT : Fin wT → ℕ} {rP : Fin wP → ℕ} {C : TableSpec}
  {R : RecordView F K Kio Kfp Key C (shapeVCL hT hP wT wP rT rP) hC mVCL} {Z : SeedSpec frameVCL K Kfp}
  {I : IOCoinSpec frameVCL K Kio}
  (CF : CompSoundnessFamily F K Kio Kfp Key frameVCL hC (shapeVCL hT hP wT wP rT rP) C 3 R Z I)
  (MF : MemSoundnessFamily F K Kio Kfp Key frameVCL hC (shapeVCL hT hP wT wP rT rP) C 3 R Z I)

/-- **`epsilon_vcl_le`'s walk twin**: the memory summands carry the walk event `15W/|𝕂|` beside the
seeds, and the IO totals are `totVCLW` (table `1` rows = walk rows `W`). -/
theorem epsilon_vclW_le (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) (x : CF.Msg0)
    (y : MF.Msg0) (hN : 0 < V.N)
    (hMF : epsilonOf (MF.summands V y) ≤
      ((1 + memSeedWork V.N (cellRows V) (2 ^ 110) : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 2 +
        ((15 * pathRows V : ℕ) : ℚ) / (Fintype.card K : ℚ))
    (hCF : epsilonOf (CF.summands V x) ≤
      ((12 * V.N + 11 : ℕ) : ℚ) / (Fintype.card K : ℚ) + 1 / (Fintype.card K : ℚ) ^ 2)
    (hZ : Z.dep.card = 2)
    (hW : MF.windowBound V y = 2 ^ 110)
    (hI : I.dep.card = 4) (hKio : Fintype.card Kio = Fintype.card K ^ 2)
    (hinl : CF.inlinePairCount = 0)
    (htot : ∀ a, (CF.reqBound V a + MF.internalBound V a) + MF.respBound V a ≤
      totVCLW V.N (cellRows V) (pathRows V) a) :
    epsilonOf (allSummands (CF := CF) (MF := MF) V x y (jointSummandsStd CF MF)) ≤
      boundVCLW'' (Fintype.card K) V.N (cellRows V) (pathRows V)
        (leafBoundF (ringChar Kfp) V.N V.claim) (2 ^ 110) := by
  have hc : (Fintype.card K : ℚ) ≠ 0 := by
    have := Fintype.card_pos (α := K); positivity
  have hc1 : (1 : ℚ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  have hcp : (0 : ℚ) < Fintype.card K := lt_of_lt_of_le one_pos hc1
  have hio : ∀ a, (((ioSummand CF MF V x y a).weight : ℕ) : ℚ) /
        (Fintype.card K : ℚ) ^ (ioSummand CF MF V x y a).coins.card ≤
      (ioFailureUnionBound (mVCL a) 0 (totVCLW V.N (cellRows V) (pathRows V) a) 1 : ℚ) /
        (Fintype.card K : ℚ) ^ 2 := by
    intro a
    rw [ioSummand_mass_ext CF MF V x y a hI hKio, ioFailureUnionBound_eq_zero_add]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast ioFailureUnionBound_mono_tot _ _ (htot a)
  have hWw : windowW MF V y = max (leafBoundF (ringChar Kfp) V.N V.claim) (2 ^ 110) := by
    rw [windowW, hW]
  have hslack : 2 * (1 / (Fintype.card K : ℚ) ^ 2) ≤ ((24 * V.N : ℕ) : ℚ) / (Fintype.card K : ℚ) := by
    rw [← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) hcp]
    have hN1 : (1 : ℚ) ≤ V.N := by exact_mod_cast hN
    push_cast
    nlinarith
  have h0 := hio 0
  have h1 := hio 1
  have h2 := hio 2
  unfold allSummands
  rw [epsilonOf_append, epsilonOf_append]
  generalize epsilonOf (CF.summands V x) = eC at hCF ⊢
  generalize epsilonOf (MF.summands V y) = eM at hMF ⊢
  simp only [jointSummandsStd, jointSummands, epsilonOf, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.ofFn_succ, List.ofFn_zero]
  simp only [zeroSummand, lowSummand, censusSummand, recSummand, rootSummand, inlineSummand,
    seedSummand, hZ, hinl, hWw]
  simp only [boundVCLW'', boundGen, ioWorkKpW, jointSeedWork, mVCL, VclL.RV.mVCL, totVCLW,
    computeWork] at *
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_two,
    Matrix.tail_cons] at *
  push_cast at *
  simp only [div_eq_mul_inv, add_mul] at *
  linarith

end Eps

noncomputable section
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (hT hP hC kr : ℕ)

/-- The UNCHANGED tower compute family, at the walk memory shape. -/
abbrev CFvW : CompSoundnessFamily F K (Quad (algebraMap F K δF)) (Quad (algebraMap F K δF)) VclL.RV.KeyVCL
    frameVCL hC (shapeVW hT hP) (tableVCLT hC) 3 (m := VclL.RV.mVCL)
    (VclL.RV.recordViewVCL F K (Quad (algebraMap F K δF)) (tableVCLT hC) (shapeVW hT hP) hC)
    (ChipRAP.seedSpecVCL (algebraMap F K δF)) (ioSpecVCLQuad (algebraMap F K δF)) :=
  compSoundnessVCLT F K hC (shapeVW hT hP) δF

abbrev MFvW : MemSoundnessFamily F K (Quad (algebraMap F K δF)) (Quad (algebraMap F K δF)) VclL.RV.KeyVCL
    frameVCL hC (shapeVW hT hP) (tableVCLT hC) 3 (m := VclL.RV.mVCL)
    (VclL.RV.recordViewVCL F K (Quad (algebraMap F K δF)) (tableVCLT hC) (shapeVW hT hP) hC)
    (ChipRAP.seedSpecVCL (algebraMap F K δF)) (ioSpecVCLQuad (algebraMap F K δF)) :=
  ChipRAP.memSoundnessVCLW δF hT hP kr

theorem decodedNounW_bounded (V : VerifierData F K hC (shapeVW hT hP))
    (b : ∀ t : Fin (shapeVW hT hP).k, B0Cols F ((shapeVW hT hP).table t)) (i : ℕ) :
    FieldEmbedding.BoundedBy (ringChar F) (decodedNounW hT hP V b i) := by
  haveI : NeZero (ringChar F) := ⟨CharP.char_ne_zero_of_finite F (ringChar F)⟩
  unfold decodedNounW
  split
  · rename_i n hn
    unfold capN; split_ifs
    · exact decodeB0_boundedBy _ hn
    · exact (Nat.pos_of_ne_zero (NeZero.ne (ringChar F)) : 0 < ringChar F)
  · exact (Nat.pos_of_ne_zero (NeZero.ne (ringChar F)) : 0 < ringChar F)

/-- `ExtraPremises` for the compute family and the walk memory family: all four fields discharged. -/
theorem extraPremises_vclW :
    ExtraPremises (CFvW (K := K) δF hT hP hC) (MFvW (K := K) δF hT hP hC kr) where
  reqCond := fun _ _ _ _ _ _ _ _ _ => trivial
  recKey_s9 := fun V x b S' => VclL.Compute.recKey_s9' V b S'
  served_bounded := fun V y b κ _ => by
    have hq : ringChar (Quad (algebraMap F K δF)) = ringChar F :=
      (quad_ringChar_eq (algebraMap F K δF)).trans (Algebra.ringChar_eq F K).symm
    rw [hq]
    cases κ <;> exact decodedNounW_bounded hT hP hC V b _
  char_eq := quad_ringChar_eq (algebraMap F K δF)

/-- `rowFactsAt` at the compute family over `shapeVW` (the generic-`S` theorem). -/
theorem rowFactsAt_CFvW : rowFactsAt (CFvW (K := K) δF hT hP hC) :=
  VclL.Compute.TowerD.rowFactsAt_compSoundnessVCLT F K hC (shapeVW hT hP) δF

/-- **`vcl_standaloneW` — THE END-TO-END COMPOSITION**: `standalone_generic` at the unchanged compute
family and the walk memory family. -/
theorem vcl_standaloneW :
    StandaloneThm54Statement (CFvW (K := K) δF hT hP hC) (MFvW (K := K) δF hT hP hC kr)
      (jointSummandsStd (CFvW (K := K) δF hT hP hC) (MFvW (K := K) δF hT hP hC kr)) :=
  standalone_generic (rowFactsAt_CFvW δF hT hP hC) (extraPremises_vclW δF hT hP hC kr)

open Classical in
/-- **Soundness at the walk families** (the `soundness` conjunct of `vcl_standaloneW`, unfolded). -/
theorem vcl_standaloneW_soundness
    (V : VerifierData F K hC (shapeVW hT hP))
    (hV : V.Checks (consumerBound (CFvW (K := K) δF hT hP hC) (MFvW (K := K) δF hT hP hC kr) V)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : Messages (CFvW (K := K) δF hT hP hC) (MFvW (K := K) δF hT hP hC kr)) (hst : msg.Staged) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) ≤
      epsilonOf (allSummands (CF := CFvW (K := K) δF hT hP hC) (MF := MFvW (K := K) δF hT hP hC kr) V
        msg.msg0C msg.msg0M
        (jointSummandsStd (CFvW (K := K) δF hT hP hC) (MFvW (K := K) δF hT hP hC kr))) :=
  (vcl_standaloneW δF hT hP hC kr).soundness V hV msg hst

theorem seedSpecVCL_dep_card : (ChipRAP.seedSpecVCL (algebraMap F K δF)).dep.card = 2 :=
  Finset.card_pair (by decide)

theorem hCF_instW (V : VerifierData F K hC (shapeVW hT hP)) (x : ℕ → F) :
    epsilonOf ((CFvW (K := K) δF hT hP hC).summands V x) =
      ((12 * V.N + 11 : ℕ) : ℚ) / (Fintype.card K : ℚ) + 1 / (Fintype.card K : ℚ) ^ 2 := by
  have hz : (sumZeroT (hC := hC) (S := shapeVW hT hP) (K := K) δF).coins.card = 2 :=
    seedSpecVCL_dep_card (K := K) δF
  show epsilonOf (summandsQ7T (K := K) δF V) = _
  simp only [epsilonOf, summandsQ7T, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have hw : (sumZeroT (hC := hC) (S := shapeVW hT hP) (K := K) δF).weight = 1 := rfl
  have h1 : (sumTilingT (hC := hC) (S := shapeVW hT hP) (K := K) δF V).weight = 2 * V.N + 2 := rfl
  have h2 : (sumAlphaRootT (hC := hC) (S := shapeVW hT hP) (K := K) δF V).weight = V.N := rfl
  have h3 : (sumGammaRootT (hC := hC) (S := shapeVW hT hP) (K := K) δF V).weight = 9 := rfl
  have h4 : (sumPrefixT (hC := hC) (S := shapeVW hT hP) (K := K) δF V).weight = V.N * 9 := rfl
  have c1 : (sumTilingT (hC := hC) (S := shapeVW hT hP) (K := K) δF V).coins.card = 1 := rfl
  have c2 : (sumAlphaRootT (hC := hC) (S := shapeVW hT hP) (K := K) δF V).coins.card = 1 := rfl
  have c3 : (sumGammaRootT (hC := hC) (S := shapeVW hT hP) (K := K) δF V).coins.card = 1 := rfl
  have c4 : (sumPrefixT (hC := hC) (S := shapeVW hT hP) (K := K) δF V).coins.card = 1 := rfl
  rw [hw, h1, h2, h3, h4, hz, c1, c2, c3, c4]
  push_cast
  ring

theorem hMF_instW (V : VerifierData F K hC (shapeVW hT hP)) (y : Unit) :
    epsilonOf ((MFvW (K := K) δF hT hP hC kr).summands V y) =
      ((1 + memSeedWork V.N (cellRows V) (2 ^ 110) : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 2 +
        ((15 * pathRows V : ℕ) : ℚ) / (Fintype.card K : ℚ) := by
  show epsilonOf (vclSummandsW (C := tableVCLT hC) δF hT hP kr V y) = _
  have hz : (zeroSummand (F := F) (C := tableVCLT hC) (S := shapeVW hT hP)
      (Z := ChipRAP.seedSpecVCL (algebraMap F K δF))).coins.card = 2 := seedSpecVCL_dep_card (K := K) δF
  have hc : (vclCensusW (C := tableVCLT hC) δF hT hP V).coins.card = 2 :=
    (VclL.vclCensusSummand_shape _ _ _ _ _ _ _ _ _).1
  have hd : (vclDyckW (C := tableVCLT hC) δF hT hP V).coins.card = 2 :=
    (VclL.vclCellDyckRootSummand_shape _ _ _ _ _ _).1
  have hwS := vclWalkSummandW_shape δF hT hP kr V (C := tableVCLT hC)
  have hwc : (vclCensusW (C := tableVCLT hC) δF hT hP V).weight =
      VclL.pairCount (V.memRows (tCW hT hP) + (3 + 19 * V.N)) * (2 * VclL.fuelChip - 1) := rfl
  have hwd : (vclDyckW (C := tableVCLT hC) δF hT hP V).weight =
      V.memRows (tCW hT hP) * (2 * 2 ^ 110 - 1) := rfl
  have hwz : (zeroSummand (F := F) (C := tableVCLT hC) (S := shapeVW hT hP)
      (Z := ChipRAP.seedSpecVCL (algebraMap F K δF))).weight = 1 := rfl
  simp only [epsilonOf, vclSummandsW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [hz, hc, hd, hwc, hwd, hwz, hwS.1, hwS.2.2]
  have e : (1 + memSeedWork V.N (cellRows V) (2 ^ 110) : ℕ) =
      1 + (VclL.pairCount (V.memRows (tCW hT hP) + (3 + 19 * V.N)) * (2 * VclL.fuelChip - 1) +
        V.memRows (tCW hT hP) * (2 * 2 ^ 110 - 1)) := by
    rw [← memSeedWork_fuelChip]; rfl
  have ew : pathRows V = V.memRows (tWW hT hP) := rfl
  rw [e, ew]
  have hcK : (Fintype.card K : ℚ) ≠ 0 := by
    have := Fintype.card_pos (α := K); positivity
  push_cast
  field_simp
  ring

theorem htot_instW (V : VerifierData F K hC (shapeVW hT hP)) (a : Fin 3) :
    ((CFvW (K := K) δF hT hP hC).reqBound V a + (MFvW (K := K) δF hT hP hC kr).internalBound V a) +
      (MFvW (K := K) δF hT hP hC kr).respBound V a ≤ totVCLW V.N (cellRows V) (pathRows V) a := by
  show VclL.Compute.CompChipVCL.reqBoundCF V a + vclInternalBoundW hT hP V a + vclRespBoundW hT hP V a ≤ _
  fin_cases a <;>
    simp [VclL.Compute.CompChipVCL.reqBoundCF, vclInternalBoundW, vclRespBoundW, totVCLW, cellRows,
      pathRows, tCW, tWW] <;> omega

/-- **`ε` of the instantiated joint list is at most `boundVCLW''`.** -/
theorem vcl_epsilonW_le (V : VerifierData F K hC (shapeVW hT hP)) (x : ℕ → F) (y : Unit) :
    epsilonOf (allSummands (CF := CFvW (K := K) δF hT hP hC) (MF := MFvW (K := K) δF hT hP hC kr) V x y
        (jointSummandsStd (CFvW (K := K) δF hT hP hC) (MFvW (K := K) δF hT hP hC kr))) ≤
      boundVCLW'' (Fintype.card K) V.N (cellRows V) (pathRows V)
        (leafBoundF (ringChar (Quad (algebraMap F K δF))) V.N V.claim) (2 ^ 110) :=
  epsilon_vclW_le (CFvW (K := K) δF hT hP hC) (MFvW (K := K) δF hT hP hC kr) V x y V.hN
    (le_of_eq (hMF_instW δF hT hP hC kr V y)) (le_of_eq (hCF_instW δF hT hP hC V x))
    (seedSpecVCL_dep_card (K := K) δF) rfl (ioSpecVCLQuad_dep_card _) (quad_card _) rfl
    (htot_instW δF hT hP hC kr V)

open Classical in
/-- **Soundness at the walk families with its `ε`**: probability of the bad event at most
`boundVCLW''`.  Hypotheses: `hV` (`Checks`), `hst` (`msg.Staged`) only. -/
theorem vcl_standaloneW_soundness_le
    (V : VerifierData F K hC (shapeVW hT hP))
    (hV : V.Checks (consumerBound (CFvW (K := K) δF hT hP hC) (MFvW (K := K) δF hT hP hC kr) V)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : Messages (CFvW (K := K) δF hT hP hC) (MFvW (K := K) δF hT hP hC kr)) (hst : msg.Staged) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) ≤
      boundVCLW'' (Fintype.card K) V.N (cellRows V) (pathRows V)
        (leafBoundF (ringChar (Quad (algebraMap F K δF))) V.N V.claim) (2 ^ 110) :=
  (vcl_standaloneW_soundness δF hT hP hC kr V hV msg hst).trans
    (vcl_epsilonW_le δF hT hP hC kr V msg.msg0C msg.msg0M)

open Classical in
/-- **155 bits** at `N, D, W ≤ 2^31` (`W` = walk rows = `pathRows V`, table `1` of `shapeVW`). -/
theorem vcl_standaloneW_155'
    (V : VerifierData F K hC (shapeVW hT hP))
    (hV : V.Checks (consumerBound (CFvW (K := K) δF hT hP hC) (MFvW (K := K) δF hT hP hC kr) V)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : Messages (CFvW (K := K) δF hT hP hC) (MFvW (K := K) δF hT hP hC kr)) (hst : msg.Staged)
    (hcK : Fintype.card K = cK)
    (hN : V.N ≤ 2 ^ 31) (hD : cellRows V ≤ 2 ^ 31) (hW : pathRows V ≤ 2 ^ 31)
    (hΛ : leafBoundF (ringChar (Quad (algebraMap F K δF))) V.N V.claim ≤ 2 ^ 110) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) < 1 / (2 : ℚ) ^ 155 := by
  refine lt_of_le_of_lt (vcl_standaloneW_soundness_le δF hT hP hC kr V hV msg hst) ?_
  rw [hcK]; exact figVCLW''_two_pow_31 _ _ _ _ hN hD hW hΛ

open Classical in
/-- **154 bits** at `N, D, W ≤ 2^32`. -/
theorem vcl_standaloneW_154'
    (V : VerifierData F K hC (shapeVW hT hP))
    (hV : V.Checks (consumerBound (CFvW (K := K) δF hT hP hC) (MFvW (K := K) δF hT hP hC kr) V)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : Messages (CFvW (K := K) δF hT hP hC) (MFvW (K := K) δF hT hP hC kr)) (hst : msg.Staged)
    (hcK : Fintype.card K = cK)
    (hN : V.N ≤ 2 ^ 32) (hD : cellRows V ≤ 2 ^ 32) (hW : pathRows V ≤ 2 ^ 32)
    (hΛ : leafBoundF (ringChar (Quad (algebraMap F K δF))) V.N V.claim ≤ 2 ^ 110) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) < 1 / (2 : ℚ) ^ 154 := by
  refine lt_of_le_of_lt (vcl_standaloneW_soundness_le δF hT hP hC kr V hV msg hst) ?_
  rw [hcK]; exact figVCLW''_two_pow_32 _ _ _ _ hN hD hW hΛ

open Classical in
/-- **164 bits** at `N ≤ 2^21`, `D ≤ 2^20`, `W ≤ 2^21`. -/
theorem vcl_standaloneW_164'
    (V : VerifierData F K hC (shapeVW hT hP))
    (hV : V.Checks (consumerBound (CFvW (K := K) δF hT hP hC) (MFvW (K := K) δF hT hP hC kr) V)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : Messages (CFvW (K := K) δF hT hP hC) (MFvW (K := K) δF hT hP hC kr)) (hst : msg.Staged)
    (hcK : Fintype.card K = cK)
    (hN : V.N ≤ 2 ^ 21) (hD : cellRows V ≤ 2 ^ 20) (hW : pathRows V ≤ 2 ^ 21)
    (hΛ : leafBoundF (ringChar (Quad (algebraMap F K δF))) V.N V.claim ≤ 2 ^ 110) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) < 1 / (2 : ℚ) ^ 164 := by
  refine lt_of_le_of_lt (vcl_standaloneW_soundness_le δF hT hP hC kr V hV msg hst) ?_
  rw [hcK]; exact figVCLW''_kernel _ _ _ _ hN hD hW hΛ

end

end Nock.NockVMROM.Thm54.VclL.StandaloneW
