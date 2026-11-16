/-
  Nock/RedTeam/Batch1880Thm54VclIntegrateStandalone.lean

  **`standalone_generic` at the two VCL families
  (soundness only).**  `CF := compSoundnessVCLT`, `MF := memSoundnessVCL`, `frameVCL`,
  `Z := seedSpecVCL`, `I := ioSpecVCLQuad`, `S := shapeV hT hP`, `C := tableVCLT hC`.  Z / I / frame
  unify.

  * `extraPremises_vcl`: all four `ExtraPremises` fields discharged (`reqCond` is `True`;
    `recKey_s9'`; `decodedNoun_bounded`; `quad_ringChar_eq`).
  * `vcl_standalone_soundness`: `(standalone_generic hrow hP).soundness`.
  * `vcl_epsilon_le`: eps <= `boundVCL''`.  `epsilon_vcll_eq_quad` does NOT apply verbatim (three
    mismatches, all in the safe direction, see `epsilon_vcl_le`): `MF.summands` = [zero, census, dyck]
    (extra zero-seed summand, `1/|K|^2`) while the lemma wants `vclMemSummands` = [census, dyck];
    `CF.summands` = tower summands (zero seed `1/|K|^2` + `(12N+11)/|K|`, no topology `24N`) while the
    lemma wants `computeWork N / |K|` = `(36N+11)/|K|`; `htot` is false at accumulator 0
    (`htot_equality_fails`: reqBound 0 = 0, so 3D vs 3D+2).  The `24N/|K|` slack absorbs the two extra
    `1/|K|^2`.
  * `vcl_standalone_soundness_le`, `vcl_standalone_{155,154,164}`.
  * Hypotheses LEFT: `hrow : rowFactsAt CFv` (no tower analogue of `rowFacts_outside_core` exists
    yet), `hV : V.Checks`, `hst : msg.Staged`; figures also `|K| = cK`, `leafBoundF <= 2^110`, size bounds.
  * Honest fields not used (soundness half only).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerCompFamilyT
import Nock.NockVMROM.Thm54.VclL.Chips.MemSoundnessVCL
import Nock.NockVMROM.Thm54.P8Core.SVFrame.StandaloneGeneric
import Nock.NockVMROM.Thm54.VclL.Chips.Prelim

set_option autoImplicit false

namespace Nock.RedTeam.Batch1880

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Events
open Nock.NockVMROM.Thm54.FiniteIO

noncomputable section
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (hT hP hC : ℕ)


abbrev CFv : CompSoundnessFamily F K (Quad (algebraMap F K δF)) (Quad (algebraMap F K δF)) VclL.RV.KeyVCL frameVCL hC
    (shapeV hT hP) (tableVCLT hC) 3 (m := VclL.RV.mVCL)
    (VclL.RV.recordViewVCL F K (Quad (algebraMap F K δF)) (tableVCLT hC) (shapeV hT hP) hC)
    (ChipRAP.seedSpecVCL (algebraMap F K δF)) (ioSpecVCLQuad (algebraMap F K δF)) :=
  compSoundnessVCLT F K hC (shapeV hT hP) δF

abbrev MFv : MemSoundnessFamily F K (Quad (algebraMap F K δF)) (Quad (algebraMap F K δF)) VclL.RV.KeyVCL frameVCL hC
    (shapeV hT hP) (tableVCLT hC) 3 (m := VclL.RV.mVCL)
    (VclL.RV.recordViewVCL F K (Quad (algebraMap F K δF)) (tableVCLT hC) (shapeV hT hP) hC)
    (ChipRAP.seedSpecVCL (algebraMap F K δF)) (ioSpecVCLQuad (algebraMap F K δF)) :=
  ChipRAP.memSoundnessVCL δF hT hP



theorem decodedNoun_bounded (V : VerifierData F K hC (shapeV hT hP))
    (b : ∀ t : Fin (shapeV hT hP).k, B0Cols F ((shapeV hT hP).table t)) (i : ℕ) :
    FieldEmbedding.BoundedBy (ringChar F) (decodedNoun hT hP V b i) := by
  haveI : NeZero (ringChar F) := ⟨CharP.char_ne_zero_of_finite F (ringChar F)⟩
  unfold decodedNoun
  split
  · rename_i n hn
    unfold capN; split_ifs
    · exact decodeB0_boundedBy _ hn
    · exact (Nat.pos_of_ne_zero (NeZero.ne (ringChar F)) : 0 < ringChar F)
  · exact (Nat.pos_of_ne_zero (NeZero.ne (ringChar F)) : 0 < ringChar F)

/-- `ExtraPremises` for the two VCL families, minus nothing: all four fields are discharged. -/
theorem extraPremises_vcl : ExtraPremises (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC) where
  reqCond := fun _ _ _ _ _ _ _ _ _ => trivial
  recKey_s9 := fun V x b S' => VclL.Compute.recKey_s9' V b S'
  served_bounded := fun V y b κ _ => by
    have hq : ringChar (Quad (algebraMap F K δF)) = ringChar F :=
      (quad_ringChar_eq (algebraMap F K δF)).trans (Algebra.ringChar_eq F K).symm
    rw [hq]
    cases κ <;> exact decodedNoun_bounded hT hP hC V b _
  char_eq := quad_ringChar_eq (algebraMap F K δF)

open Classical in
/-- **Soundness at the two VCL families**: accepted outside the joint bad event => the claim holds. -/
theorem vcl_standalone_soundness
    (hrow : rowFactsAt (CFv (K := K) δF hT hP hC)) (hPrem : ExtraPremises (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC))
    (V : VerifierData F K hC (shapeV hT hP))
    (hV : V.Checks (consumerBound (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC) V)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : Messages (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC)) (hst : msg.Staged) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) ≤
      epsilonOf (allSummands (CF := CFv (K := K) δF hT hP hC) (MF := MFv (K := K) δF hT hP hC) V msg.msg0C msg.msg0M
        (jointSummandsStd (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC))) :=
  (standalone_generic hrow hPrem).soundness V hV msg hst


section Eps
variable {F K Kio Kfp Key : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [Fintype F] [Field Kfp] [DecidableEq Key]
  [Fintype Kfp] [DecidableEq Kfp] [Field Kio] [Fintype Kio] [DecidableEq Kio] [Algebra F Kio]
  {hC hT hP wT wP : ℕ} {rT : Fin wT → ℕ} {rP : Fin wP → ℕ} {C : TableSpec}
  {R : RecordView F K Kio Kfp Key C (shapeVCL hT hP wT wP rT rP) hC mVCL} {Z : SeedSpec frameVCL K Kfp}
  {I : IOCoinSpec frameVCL K Kio}
  (CF : CompSoundnessFamily F K Kio Kfp Key frameVCL hC (shapeVCL hT hP wT wP rT rP) C 3 R Z I)
  (MF : MemSoundnessFamily F K Kio Kfp Key frameVCL hC (shapeVCL hT hP wT wP rT rP) C 3 R Z I)

/-- **`epsilon_vcll_eq` weakened to `≤`**, for the instance whose summand lists are NOT the ones the
equality lemma assumes: the compute side has an extra zero-seed summand and no topology `24N`; the
memory side has an extra zero-seed summand; `reqBound 0 = 0`. -/
theorem epsilon_vcl_le (V : VerifierData F K hC (shapeVCL hT hP wT wP rT rP)) (x : CF.Msg0)
    (y : MF.Msg0) (hN : 0 < V.N)
    (hMF : epsilonOf (MF.summands V y) ≤
      ((1 + memSeedWork V.N (cellRows V) (2 ^ 110) : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 2)
    (hCF : epsilonOf (CF.summands V x) ≤
      ((12 * V.N + 11 : ℕ) : ℚ) / (Fintype.card K : ℚ) + 1 / (Fintype.card K : ℚ) ^ 2)
    (hZ : Z.dep.card = 2)
    (hW : MF.windowBound V y = 2 ^ 110)
    (hI : I.dep.card = 4) (hKio : Fintype.card Kio = Fintype.card K ^ 2)
    (hinl : CF.inlinePairCount = 0)
    (htot : ∀ a, (CF.reqBound V a + MF.internalBound V a) + MF.respBound V a ≤
      totVCLS V.N (cellRows V) (pathRows V) a) :
    epsilonOf (allSummands (CF := CF) (MF := MF) V x y (jointSummandsStd CF MF)) ≤
      boundVCL'' (Fintype.card K) V.N (cellRows V) (pathRows V)
        (leafBoundF (ringChar Kfp) V.N V.claim) (2 ^ 110) := by
  have hc : (Fintype.card K : ℚ) ≠ 0 := by
    have := Fintype.card_pos (α := K); positivity
  have hc1 : (1 : ℚ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  have hcp : (0 : ℚ) < Fintype.card K := lt_of_lt_of_le one_pos hc1
  have hio : ∀ a, (((ioSummand CF MF V x y a).weight : ℕ) : ℚ) /
        (Fintype.card K : ℚ) ^ (ioSummand CF MF V x y a).coins.card ≤
      (ioFailureUnionBound (mVCL a) 0 (totVCLS V.N (cellRows V) (pathRows V) a) 1 : ℚ) /
        (Fintype.card K : ℚ) ^ 2 := by
    intro a
    rw [ioSummand_mass_ext CF MF V x y a hI hKio, ioFailureUnionBound_eq_zero_add]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast ioFailureUnionBound_mono_tot _ _ (htot a)
  have hWw : windowW MF V y = max (leafBoundF (ringChar Kfp) V.N V.claim) (2 ^ 110) := by
    rw [windowW, hW]
  have hcoin : ∀ a, (ioSummand CF MF V x y a).coins.card = 4 := fun _ => hI
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
  simp only [boundVCL'', boundGen, ioWorkKpS, jointSeedWork, mVCL, VclL.RV.mVCL, totVCLS, computeWork] at *
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_two,
    Matrix.tail_cons] at *
  push_cast at *
  simp only [div_eq_mul_inv, add_mul] at *
  linarith

end Eps

end

section Inst
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (hT hP hC : ℕ)

theorem seedSpecVCL_dep_card : (ChipRAP.seedSpecVCL (algebraMap F K δF)).dep.card = 2 :=
  Finset.card_pair (by decide)

theorem hCF_inst (V : VerifierData F K hC (shapeV hT hP)) (x : ℕ → F) :
    epsilonOf ((CFv (K := K) δF hT hP hC).summands V x) =
      ((12 * V.N + 11 : ℕ) : ℚ) / (Fintype.card K : ℚ) + 1 / (Fintype.card K : ℚ) ^ 2 := by
  have hz : (sumZeroT (hC := hC) (S := shapeV hT hP) (K := K) δF).coins.card = 2 :=
    seedSpecVCL_dep_card (K := K) δF
  show epsilonOf (summandsQ7T (K := K) δF V) = _
  simp only [epsilonOf, summandsQ7T, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have hw : (sumZeroT (hC := hC) (S := shapeV hT hP) (K := K) δF).weight = 1 := rfl
  have h1 : (sumTilingT (hC := hC) (S := shapeV hT hP) (K := K) δF V).weight = 2 * V.N + 2 := rfl
  have h2 : (sumAlphaRootT (hC := hC) (S := shapeV hT hP) (K := K) δF V).weight = V.N := rfl
  have h3 : (sumGammaRootT (hC := hC) (S := shapeV hT hP) (K := K) δF V).weight = 9 := rfl
  have h4 : (sumPrefixT (hC := hC) (S := shapeV hT hP) (K := K) δF V).weight = V.N * 9 := rfl
  have c1 : (sumTilingT (hC := hC) (S := shapeV hT hP) (K := K) δF V).coins.card = 1 := rfl
  have c2 : (sumAlphaRootT (hC := hC) (S := shapeV hT hP) (K := K) δF V).coins.card = 1 := rfl
  have c3 : (sumGammaRootT (hC := hC) (S := shapeV hT hP) (K := K) δF V).coins.card = 1 := rfl
  have c4 : (sumPrefixT (hC := hC) (S := shapeV hT hP) (K := K) δF V).coins.card = 1 := rfl
  rw [hw, h1, h2, h3, h4, hz, c1, c2, c3, c4]
  push_cast
  ring

theorem hMF_inst (V : VerifierData F K hC (shapeV hT hP)) (y : Unit) :
    epsilonOf ((MFv (K := K) δF hT hP hC).summands V y) =
      ((1 + memSeedWork V.N (cellRows V) (2 ^ 110) : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 2 := by
  show epsilonOf (vclSummands (C := tableVCLT hC) δF hT hP V y) = _
  have hz : (zeroSummand (F := F) (C := tableVCLT hC) (S := shapeV hT hP)
      (Z := ChipRAP.seedSpecVCL (algebraMap F K δF))).coins.card = 2 := seedSpecVCL_dep_card (K := K) δF
  have hc : (vclCensus (C := tableVCLT hC) δF hT hP V).coins.card = 2 :=
    (VclL.vclCensusSummand_shape _ _ _ _ _ _ _ _ _).1
  have hd : (vclDyck (C := tableVCLT hC) δF hT hP V).coins.card = 2 :=
    (VclL.vclCellDyckRootSummand_shape _ _ _ _ _ _).1
  have hwc : (vclCensus (C := tableVCLT hC) δF hT hP V).weight =
      VclL.pairCount (V.memRows (tC hT hP) + (3 + 19 * V.N)) * (2 * VclL.fuelChip - 1) := rfl
  have hwd : (vclDyck (C := tableVCLT hC) δF hT hP V).weight =
      V.memRows (tC hT hP) * (2 * 2 ^ 110 - 1) := rfl
  have hwz : (zeroSummand (F := F) (C := tableVCLT hC) (S := shapeV hT hP)
      (Z := ChipRAP.seedSpecVCL (algebraMap F K δF))).weight = 1 := rfl
  simp only [epsilonOf, vclSummands, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [hz, hc, hd, hwc, hwd, hwz]
  have := memSeedWork_fuelChip V.N (cellRows V) 
  have e : (1 + memSeedWork V.N (cellRows V) (2 ^ 110) : ℕ) =
      1 + (VclL.pairCount (V.memRows (tC hT hP) + (3 + 19 * V.N)) * (2 * VclL.fuelChip - 1) +
        V.memRows (tC hT hP) * (2 * 2 ^ 110 - 1)) := by
    rw [← memSeedWork_fuelChip]; rfl
  rw [e]
  push_cast
  ring

theorem htot_inst (V : VerifierData F K hC (shapeV hT hP)) (a : Fin 3) :
    ((CFv (K := K) δF hT hP hC).reqBound V a + (MFv (K := K) δF hT hP hC).internalBound V a) +
      (MFv (K := K) δF hT hP hC).respBound V a ≤ totVCLS V.N (cellRows V) (pathRows V) a := by
  show VclL.Compute.CompChipVCL.reqBoundCF V a + vclInternalBound hT hP V a + vclRespBound hT hP V a ≤ _
  fin_cases a <;>
    simp [VclL.Compute.CompChipVCL.reqBoundCF, vclInternalBound, vclRespBound, totVCLS, cellRows, pathRows, tC, tP] <;> omega

/-- **`ε` of the instantiated joint list is at most `boundVCL''`** (`epsilon_vcll_eq_quad` does not apply
verbatim: see the module doc; this is its `≤` form, `epsilon_vcl_le`, every hypothesis discharged). -/
theorem vcl_epsilon_le (V : VerifierData F K hC (shapeV hT hP)) (x : ℕ → F) (y : Unit) :
    epsilonOf (allSummands (CF := CFv (K := K) δF hT hP hC) (MF := MFv (K := K) δF hT hP hC) V x y
        (jointSummandsStd (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC))) ≤
      boundVCL'' (Fintype.card K) V.N (cellRows V) (pathRows V)
        (leafBoundF (ringChar (Quad (algebraMap F K δF))) V.N V.claim) (2 ^ 110) :=
  epsilon_vcl_le (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC) V x y V.hN
    (le_of_eq (hMF_inst δF hT hP hC V y)) (le_of_eq (hCF_inst δF hT hP hC V x))
    (seedSpecVCL_dep_card (K := K) δF) rfl (ioSpecVCLQuad_dep_card _) (quad_card _) rfl
    (htot_inst δF hT hP hC V)

open Classical in
/-- **The soundness theorem at the two VCL families, with its `ε`.**  Accepted outside the joint bad
event => the claim holds, with probability of the bad event at most `boundVCL''`.  Hypotheses left:
`hrow` (`rowFactsAt` at the tower compute chip), `hV` (`Checks`), `hst` (`msg.Staged`). -/
theorem vcl_standalone_soundness_le
    (hrow : rowFactsAt (CFv (K := K) δF hT hP hC))
    (V : VerifierData F K hC (shapeV hT hP))
    (hV : V.Checks (consumerBound (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC) V)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : Messages (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC)) (hst : msg.Staged) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) ≤
      boundVCL'' (Fintype.card K) V.N (cellRows V) (pathRows V)
        (leafBoundF (ringChar (Quad (algebraMap F K δF))) V.N V.claim) (2 ^ 110) :=
  (vcl_standalone_soundness δF hT hP hC hrow (extraPremises_vcl δF hT hP hC) V hV msg hst).trans
    (vcl_epsilon_le δF hT hP hC V msg.msg0C msg.msg0M)

/-- **Negative control (discriminating): `epsilon_vcll_eq_quad`'s `htot` is FALSE at these instances.**
At accumulator `0` the compute side books `reqBoundCF 0 = 0` and the memory side `2D + D`, against
`totVCLS _ D _ 0 = 3D + 2`: the equality form fails (by exactly `2`) at every `V`, so the equality
lemma cannot be applied, and `htot_inst` / `vcl_epsilon_le` use the `<=` form. -/
theorem htot_equality_fails (V : VerifierData F K hC (shapeV hT hP)) :
    ¬ ∀ a, ((CFv (K := K) δF hT hP hC).reqBound V a + (MFv (K := K) δF hT hP hC).internalBound V a) +
      (MFv (K := K) δF hT hP hC).respBound V a = totVCLS V.N (cellRows V) (pathRows V) a := by
  intro h
  have := h 0
  revert this
  show VclL.Compute.CompChipVCL.reqBoundCF V 0 + vclInternalBound hT hP V 0 + vclRespBound hT hP V 0 = _ → False
  simp [VclL.Compute.CompChipVCL.reqBoundCF, vclInternalBound, vclRespBound, totVCLS, cellRows, tC]
  omega

end Inst

section Figs
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (hT hP hC : ℕ)

open Classical in
/-- **155 bits** at `N, D, P <= 2^31` (field `K` of size `cK`, window `<= 2^110`). -/
theorem vcl_standalone_155
    (hrow : rowFactsAt (CFv (K := K) δF hT hP hC))
    (V : VerifierData F K hC (shapeV hT hP))
    (hV : V.Checks (consumerBound (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC) V)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : Messages (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC)) (hst : msg.Staged)
    (hcK : Fintype.card K = cK)
    (hN : V.N ≤ 2 ^ 31) (hD : cellRows V ≤ 2 ^ 31) (hP' : pathRows V ≤ 2 ^ 31)
    (hΛ : leafBoundF (ringChar (Quad (algebraMap F K δF))) V.N V.claim ≤ 2 ^ 110) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) < 1 / (2 : ℚ) ^ 155 := by
  refine lt_of_le_of_lt (vcl_standalone_soundness_le δF hT hP hC hrow V hV msg hst) ?_
  rw [hcK]; exact figVCL''_two_pow_31 _ _ _ _ hN hD hP' hΛ

open Classical in
/-- **154 bits** at `N, D, P <= 2^32`. -/
theorem vcl_standalone_154
    (hrow : rowFactsAt (CFv (K := K) δF hT hP hC))
    (V : VerifierData F K hC (shapeV hT hP))
    (hV : V.Checks (consumerBound (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC) V)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : Messages (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC)) (hst : msg.Staged)
    (hcK : Fintype.card K = cK)
    (hN : V.N ≤ 2 ^ 32) (hD : cellRows V ≤ 2 ^ 32) (hP' : pathRows V ≤ 2 ^ 32)
    (hΛ : leafBoundF (ringChar (Quad (algebraMap F K δF))) V.N V.claim ≤ 2 ^ 110) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) < 1 / (2 : ℚ) ^ 154 := by
  refine lt_of_le_of_lt (vcl_standalone_soundness_le δF hT hP hC hrow V hV msg hst) ?_
  rw [hcK]; exact figVCL''_two_pow_32 _ _ _ _ hN hD hP' hΛ

open Classical in
/-- **164 bits** at `N <= 2^21`, `D <= 2^20`, `P <= 2^21`. -/
theorem vcl_standalone_164
    (hrow : rowFactsAt (CFv (K := K) δF hT hP hC))
    (V : VerifierData F K hC (shapeV hT hP))
    (hV : V.Checks (consumerBound (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC) V)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : Messages (CFv (K := K) δF hT hP hC) (MFv (K := K) δF hT hP hC)) (hst : msg.Staged)
    (hcK : Fintype.card K = cK)
    (hN : V.N ≤ 2 ^ 21) (hD : cellRows V ≤ 2 ^ 20) (hP' : pathRows V ≤ 2 ^ 21)
    (hΛ : leafBoundF (ringChar (Quad (algebraMap F K δF))) V.N V.claim ≤ 2 ^ 110) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        AcceptsV V msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVCL K) < 1 / (2 : ℚ) ^ 164 := by
  refine lt_of_le_of_lt (vcl_standalone_soundness_le δF hT hP hC hrow V hV msg hst) ?_
  rw [hcK]; exact figVCL''_kernel _ _ _ _ hN hD hP' hΛ

end Figs


#print axioms vcl_standalone_soundness
#print axioms htot_equality_fails
#print axioms extraPremises_vcl
#print axioms vcl_epsilon_le
#print axioms vcl_standalone_soundness_le
#print axioms vcl_standalone_155
#print axioms vcl_standalone_154
#print axioms vcl_standalone_164

end Nock.RedTeam.Batch1880
