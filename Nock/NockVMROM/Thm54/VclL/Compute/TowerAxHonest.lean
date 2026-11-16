import Nock.NockVMROM.Thm54.VclL.Compute.TowerReadsHonest
import Nock.NockVMROM.Thm54.BelowDefs.TraceGen.GenFormRAxisLambda

/-!
# The axis-gate leaf hypotheses at generated rows (item 5)

* `honest_ax_gen`: `honest_axGates'` and `honest_axImGates` hold at the honest trace row `i` when the row is
  `genRowVals` and, at an OP0 (OP9) row, `f_t` (`f_th`) is the atom fingerprint of an axis `a` and the VCL axis
  column `221` carries `a`.  Roles `41`/`44` are the `f_t`/`f_th` leaves (`genRowVals_ext41`).
* `gen_ax_dec`: those hypotheses at a generator node (`NodeAxisInFormula`, true at every node of the
  BFS-assigned AIR-reordered tree: `genComputeSkeleton_assigned_inTree_axisInFormula`), the axis being `honestAx`.
* `honest_ax_of_gen`: the combination (fill choice: `vcl 221 = honestAx skel`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.ComputeTable Nock.Reified Module
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace Nock.NockVMROM.Thm54.OptimizedComputeCodec Nock.NockVMROM.Thm54.OptimizedComputeOverlay
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.Framework Nock.Framework.Reify

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section

section Ax
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

theorem genRowVals_ext41 (pub : Pub (Quad (algebraMap F K δ))) (dec : Dec (Quad (algebraMap F K δ)))
    (ex : Extra (Quad (algebraMap F K δ))) (i n : ℕ)
    (wc wa wln winv r58 r59 : Quad (algebraMap F K δ)) (vcl : ℕ → F) (tg : Fin 3 → Quad (algebraMap F K δ)) :
    (genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg).ext 41 = dec.f_t.leaf ∧
    (genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg).ext 44 = dec.f_th.leaf := by
  cases hs : pub.state <;>
    simp [genRowVals, coreExtensionValue, row309, sampledEncode309, sampledEncodeExtension309,
      sampledEncodeExtension, honestOverlay, overlayRoleA, overlayRoleB, overlayDenoms,
      OptimizedComputeCodec.encodeExtension, decFingerprint, fpCoordinate, hs]

theorem natCast_quad_re (a : ℕ) : Quad.re (algebraMap F K δ) ((a : ℕ) : Quad (algebraMap F K δ)) = (a : K) := by
  rw [show ((a : ℕ) : Quad (algebraMap F K δ)) = algebraMap K _ (a : K) from (map_natCast _ a).symm,
    ← Quad.mk_base, Quad.re_mk]

theorem natCast_quad_im (a : ℕ) : Quad.im (algebraMap F K δ) ((a : ℕ) : Quad (algebraMap F K δ)) = 0 := by
  rw [show ((a : ℕ) : Quad (algebraMap F K δ)) = algebraMap K _ (a : K) from (map_natCast _ a).symm,
    ← Quad.mk_base, Quad.im_mk]

/-- **The axis-gate leaf hypotheses (`honest_axGates'`, `honest_axImGates`) at a `genRowVals` row of the
honest trace.**  `hf0 / hf9`: at an OP0 (OP9) row the `f_t` (`f_th`) fingerprint is the atom fingerprint of
the axis `a` and the VCL axis column `221` carries `a` (the honest fill, `honestAx`). -/
theorem honest_ax_gen (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)
    (hinj : Function.Injective nodes) (rows : Fin n → TowerRowVals (K := K) δ) (ω : F) (cv pv : ℕ → F)
    (i : Fin n) (zq : Quad (algebraMap F K δ))
    (pub : Pub (Quad (algebraMap F K δ))) (dec : Dec (Quad (algebraMap F K δ)))
    (ex : Extra (Quad (algebraMap F K δ))) (idx N : ℕ)
    (wc wa wln winv r58 r59 : Quad (algebraMap F K δ)) (vcl : ℕ → F) (tg : Fin 3 → Quad (algebraMap F K δ))
    (hrow : rows i = genRowVals pub dec ex idx N wc wa wln winv r58 r59 vcl tg)
    (hf0 : pub.state = .s0 → ∃ a : ℕ, dec.f_t = GlobalCarryRecognizer.enc zq (.atom a) ∧ vcl 221 = (a : F))
    (hf9 : pub.state = .s9 → ∃ a : ℕ, dec.f_th = GlobalCarryRecognizer.enc zq (.atom a) ∧ vcl 221 = (a : F)) :
    (∀ g ∈ axGates b, g.eval (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv) = 0) ∧
    (∀ g ∈ (axImGates : List (CoeffExpr F)),
      g.eval (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv) = 0) := by
  set envF := Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv with henvF
  have htr : ∀ j, j < 409 → envF.trace j = vclColT b rows j i := fun j hj =>
    env_honestQT_trace b nodes hinj rows ω cv pv i (by show j < vclWidthT; simp only [vclWidthT]; omega)
  have tsel : ∀ j, j < 11 → envF.trace j = if j = (stateIndex pub.state : ℕ) then 1 else 0 := by
    intro j hj
    rw [htr j (by omega)]
    simp only [vclColT, show j < 202 by omega, if_true, srcColT, show j < 13 by omega, dif_pos, hrow]
    simp [genRowVals, hj]
  have tax : envF.trace axCol = vcl 221 := by
    rw [htr _ (by decide), vclColT_vclOnly b rows i axCol (by decide) (by right; decide), hrow]
    rfl
  have tleaf : ∀ r : Fin 63, ∀ k : Fin 3, envF.trace (13 + 3 * (r : ℕ) + k) =
      coord b (Quad.re _ ((genRowVals pub dec ex idx N wc wa wln winv r58 r59 vcl tg).ext r)) k := by
    intro r k
    have := r.isLt; have := k.isLt
    rw [htr _ (by omega), vclColT, if_pos (by omega), ← hrow, srcColT_role]
  have e41 := (genRowVals_ext41 pub dec ex idx N wc wa wln winv r58 r59 vcl tg).1
  have e44 := (genRowVals_ext41 pub dec ex idx N wc wa wln winv r58 r59 vcl tg).2
  have hft : ∀ k : Fin 3, envF.trace (ftLeafLimb k) =
      coord b (Quad.re _ dec.f_t.leaf) k := fun k => by
    have := tleaf 41 k
    rw [e41] at this
    exact this
  have hfth : ∀ k : Fin 3, envF.trace (fthLeafLimb k) =
      coord b (Quad.re _ dec.f_th.leaf) k := fun k => by
    have := tleaf 44 k
    rw [e44] at this
    exact this
  constructor
  · obtain ⟨a₀, a₉, h0, h9⟩ : ∃ a₀ a₉ : ℕ,
        (envF.trace 0 = 1 → envF.trace axCol = (a₀ : F) ∧
          ∀ k, envF.trace (ftLeafLimb k) = coord b (GlobalCarryRecognizer.enc (0 : K) (.atom a₀)).leaf k) ∧
        (envF.trace 9 = 1 → envF.trace axCol = (a₉ : F) ∧
          ∀ k, envF.trace (fthLeafLimb k) = coord b (GlobalCarryRecognizer.enc (0 : K) (.atom a₉)).leaf k) := by
      have t0 := tsel 0 (by norm_num)
      have t9 := tsel 9 (by norm_num)
      by_cases hs0 : pub.state = .s0
      · obtain ⟨a, hd, hv⟩ := hf0 hs0
        refine ⟨a, 0, fun _ => ⟨by rw [tax, hv], fun k => ?_⟩, fun h => ?_⟩
        · rw [hft, hd, enc_atom_leaf, enc_atom_leaf, natCast_quad_re]
        · rw [t9, hs0] at h; simp [stateIndex] at h
      by_cases hs9 : pub.state = .s9
      · obtain ⟨a, hd, hv⟩ := hf9 hs9
        refine ⟨0, a, fun h => ?_, fun _ => ⟨by rw [tax, hv], fun k => ?_⟩⟩
        · rw [t0, hs9] at h; simp [stateIndex] at h
        · rw [hfth, hd, enc_atom_leaf, enc_atom_leaf, natCast_quad_re]
      · refine ⟨0, 0, fun h => ?_, fun h => ?_⟩
        · rw [t0] at h
          have : (stateIndex pub.state : ℕ) = 0 := by
            by_contra hne; rw [if_neg (fun e => hne e.symm)] at h; exact zero_ne_one h
          have : pub.state = .s0 := by
            revert this; cases pub.state <;> simp [stateIndex]
          exact absurd this hs0
        · rw [t9] at h
          have : (stateIndex pub.state : ℕ) = 9 := by
            by_contra hne; rw [if_neg (fun e => hne e.symm)] at h; exact zero_ne_one h
          have : pub.state = .s9 := by
            revert this; cases pub.state <;> simp [stateIndex]
          exact absurd this hs9
    refine honest_axGates' b 0 a₀ a₉ envF ?_ ?_ h0 h9
    · rw [tsel 0 (by norm_num)]; split_ifs <;> simp
    · rw [tsel 9 (by norm_num)]; split_ifs <;> simp
  · have himk : ∀ r : Fin 63, (232 ≤ (fullImMap.ext r).getD 0 ∧ (fullImMap.ext r).getD 0 + 2 < 394 ∧
        ∀ c', fullImMap.ext r = some c' → towerM.ext r = some (c' + 95)) ∨ fullImMap.ext r = none := by
      decide +kernel
    have tim : ∀ r : Fin 63, fullImMap.ext r ≠ none → ∀ k : Fin 3,
        envF.trace ((fullImMap.ext r).getD 0 + k) =
          coord b (Quad.im _ ((genRowVals pub dec ex idx N wc wa wln winv r58 r59 vcl tg).ext r)) k := by
      intro r hr k
      rcases himk r with ⟨h1, h2, h3⟩ | h
      · obtain ⟨c', hc'⟩ : ∃ c', fullImMap.ext r = some c' := by
          cases hh : fullImMap.ext r with
          | none => exact absurd hh hr
          | some c' => exact ⟨c', rfl⟩
        have hk := k.isLt
        rw [hc'] at h1 h2 ⊢
        simp only [Option.getD_some] at h1 h2 ⊢
        rw [htr _ (by omega), vclColT, if_neg (by omega), if_pos (Or.inr ⟨by omega, by omega⟩), ← hrow,
          show c' + (k : ℕ) + 95 = (c' + 95) + (k : ℕ) by omega, srcColT_im b _ r _ (h3 c' hc') k]
      · exact absurd h hr
    have hne41 : fullImMap.ext 41 ≠ none := by decide
    have hne44 : fullImMap.ext 44 ≠ none := by decide
    have t0z : pub.state ≠ .s0 → envF.trace 0 = 0 := by
      intro hs
      rw [tsel 0 (by norm_num), if_neg]
      intro e
      apply hs
      have : (stateIndex pub.state : ℕ) = 0 := e.symm
      revert this; cases pub.state <;> simp [stateIndex]
    have t9z : pub.state ≠ .s9 → envF.trace 9 = 0 := by
      intro hs
      rw [tsel 9 (by norm_num), if_neg]
      intro e
      apply hs
      have : (stateIndex pub.state : ℕ) = 9 := e.symm
      revert this; cases pub.state <;> simp [stateIndex]
    refine honest_axImGates envF ?_ ?_
    · by_cases hs0 : pub.state = .s0
      · right
        intro k
        obtain ⟨a, hd, -⟩ := hf0 hs0
        rw [tim 41 hne41 k, e41, hd, enc_atom_leaf, natCast_quad_im]
        simp [coord]
      · left; exact t0z hs0
    · by_cases hs9 : pub.state = .s9
      · right
        intro k
        obtain ⟨a, hd, -⟩ := hf9 hs9
        rw [tim 44 hne44 k, e44, hd, enc_atom_leaf, natCast_quad_im]
        simp [coord]
      · left; exact t9z hs9

end Ax

section GenAx
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.SemanticStrategy Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]

/-- **The atom-fingerprint hypotheses at a generator row**: at an OP0 (OP9) node the rendered `f_t` (`f_th`) is
the atom fingerprint of the axis, which is `honestAx` of the skeleton (`NodeAxisInFormula`). -/
theorem gen_ax_dec (z α : L) (g : GenComputeRow L) (hshape : NodeAxisInFormula g) :
    ((renderNode z α g).row.2.2.1.state = .s0 → ∃ a : ℕ,
      (renderNode z α g).row.2.2.2.f_t = GlobalCarryRecognizer.enc z (.atom a) ∧ a = honestAx g.skel) ∧
    ((renderNode z α g).row.2.2.1.state = .s9 → ∃ a : ℕ,
      (renderNode z α g).row.2.2.2.f_th = GlobalCarryRecognizer.enc z (.atom a) ∧ a = honestAx g.skel) := by
  constructor
  · intro hs
    have hst : g.skel.state = .s0 := by rw [← renderNode_row_state z α g]; exact hs
    obtain ⟨hd, hf⟩ := hshape.1 hst
    refine ⟨P8Census.skeletonMemoryAxis g.skel 1, ?_, (honestAx_s0 hd _ g.skel hst hf).symm⟩
    rw [(renderNode_row_s0 z α g hst).2, hf, encC_eq]
    rfl
  · intro hs
    have hst : g.skel.state = .s9 := by rw [← renderNode_row_state z α g]; exact hs
    obtain ⟨hd, tt, hf⟩ := hshape.2.1 hst
    refine ⟨P8Census.skeletonMemoryAxis g.skel 2, ?_, (honestAx_s9 hd tt _ g.skel hst hf).symm⟩
    rw [(renderNode_row_s9 z α g hst).2, hf, encC_eq]
    rfl

end GenAx

section Comb
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.SemanticStrategy
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **`honest_axGates'` / `honest_axImGates` leaf hypotheses at a generator node**: the row is `genRowVals` of
the rendered node `renderNode z α g` (`g` a node of the BFS-assigned AIR-reordered tree, `NodeAxisInFormula`),
with the honest axis fill `vcl 221 = honestAx g.skel`. -/
theorem honest_ax_of_gen (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)
    (hinj : Function.Injective nodes) (rows : Fin n → TowerRowVals (K := K) δ) (ω : F) (cv pv : ℕ → F)
    (i : Fin n) (z α : Quad (algebraMap F K δ)) (g : GenComputeRow (Quad (algebraMap F K δ)))
    (hshape : NodeAxisInFormula g) (ex : Extra (Quad (algebraMap F K δ))) (idx N : ℕ)
    (wc wa wln winv r58 r59 : Quad (algebraMap F K δ)) (vcl : ℕ → F) (tg : Fin 3 → Quad (algebraMap F K δ))
    (hrow : rows i = genRowVals (renderNode z α g).row.2.2.1 (renderNode z α g).row.2.2.2 ex idx N
      wc wa wln winv r58 r59 vcl tg)
    (hvcl : vcl 221 = (honestAx g.skel : F)) :
    (∀ g' ∈ axGates b, g'.eval (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv) = 0) ∧
    (∀ g' ∈ (axImGates : List (CoeffExpr F)),
      g'.eval (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv) = 0) := by
  obtain ⟨h0, h9⟩ := gen_ax_dec z α g hshape
  exact honest_ax_gen b nodes hinj rows ω cv pv i z _ _ ex idx N wc wa wln winv r58 r59 vcl tg hrow
    (fun hs => by obtain ⟨a, hd, ha⟩ := h0 hs; exact ⟨a, hd, by rw [hvcl, ha]⟩)
    (fun hs => by obtain ⟨a, hd, ha⟩ := h9 hs; exact ⟨a, hd, by rw [hvcl, ha]⟩)

/-- **NC (the axis column discriminates)**: at an OP0 row whose `f_t` leaf is the atom `a`, an axis column off
by one fails the axis gate coordinate (`coord 1 k ≠ 0`). -/
theorem nc_ax_off_by_one (b : Basis (Fin 3) F K) (envF : Env F) (a : ℕ) (k : Fin 3)
    (hk : coord b 1 k ≠ 0) (h0 : envF.trace 0 = 1) (h9 : envF.trace 9 = 0)
    (hax : envF.trace axCol = (a : F) + 1) (hleaf : envF.trace (ftLeafLimb k) = (a : F) * coord b 1 k) :
    (axGateCoord b k).eval envF ≠ 0 := by
  rw [axGateCoord_eval, h0, h9, hax, hleaf]
  intro h
  apply hk
  linear_combination -h

end Comb

section FirstAssembly
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.ComputeWalkLabel Nock.Walk Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.OptimizedComputeCodec
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **`FirstReads` at the honest tower env, from its content fields** (the first-row analogue of
`nextReads_of_fill`): the masks `20 + opCol` from the bank placement (`firstSel_of_bank`), `α` and `γ` from the
challenge placement; the restored sources (`firstSrc_of_fill` discharges them at a `genRowVals` row) and the
hosted child tags (FALSE at `genRowVals` as defined, see `honestOverlay_tag_ne_childStateTagCol`) stay hypotheses. -/
theorem firstReads_of_fill (b : Basis (Fin 3) F K) (χ : Coins frameVCL K)
    (D : HonestWalk (Quad (algebraMap F K δ))) (eF : Env F) (hch : eF.chal = chalVQ7T δ b χ)
    (s0 : ℕ) (hs0 : s0 = (stateIndex (D.pubAt 0).state : ℕ))
    (hbank : ∀ j, j < 11 → eF.pub (20 + j) = if j = s0 then 1 else 0)
    (hα : D.α = algebraMap K _ (χ ⟨0, by decide⟩)) (hγ : D.γ = algebraMap K _ (χ ⟨1, by decide⟩))
    (hsrc : ∀ (role c : ℕ) (hr : role < 12) (hc : c < 3),
      (sourcePubAtR curReader (D.pubAt 0).state role c).eval
          (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv =
        fpCoordinate (pubFingerprint (D.pubAt 0) ⟨role, hr⟩) ⟨c, hc⟩)
    (htag : ∀ k : Fin 3, (childTagHost curReader (D.pubAt 0).state k).eval
          (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv = childStateTagCol D.W 1 k) :
    FirstReads D (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv := by
  have hchal := towerEnv309_chal_placement δ b χ eF hch
  refine ⟨firstSel_of_bank b eF s0 (D.pubAt 0).state hs0 hbank, hsrc, htag, ?_, ?_⟩
  · show (walkChallenge 0).eval (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv = D.α
    rw [hα, ← hchal.2.2.2.2.2.1]
    simp [walkChallenge, walkChallengeBase, Expr.eval, Env309.toSourceEnv,
      CorrectedFinalTypedEnv.toSourceEnv]
  · rw [hγ, ← hchal.2.2.2.2.2.2]
    simp [walkGammaChallenge, ComputeWalkLabel.walkGammaChallengeIndex, Expr.eval, Env309.toSourceEnv,
      CorrectedFinalTypedEnv.toSourceEnv]

end FirstAssembly

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
