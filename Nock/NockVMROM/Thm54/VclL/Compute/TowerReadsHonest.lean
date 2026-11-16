import Nock.NockVMROM.Thm54.VclL.Compute.TowerWalkGen
import Nock.NockVMROM.Thm54.TraceGen.GenClaimedResult
import Nock.NockVMROM.Thm54.TraceGen.GenRootState

/-!

* `curSrc_of_reads`: the restored public sources `sourcePubAtR curReader pub.state role c` evaluate to the
  row's fingerprint coordinates at ANY env that reads the one-hot selectors and the 54 public/dec
  roles `0..53` of the un-hosted 309 row, given `V_comp` (A-free; routes through `Row309Reads.semPub`).
* `nextSrc_of_fill` / `firstSrc_of_fill`: the same at `shiftNext` (successor row, from `hFn`) and at the
  current row (first row, from `hF`) of the honest tower env, with the row filled by `genRowVals`.
* `firstSel_of_bank`: the first-row masks `pub (20 + opCol)` from the public bank placement.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.ComputeTable Nock.Reified Module
open Nock.NockVMROM.Thm54.OptimizedComputeCodec Nock.NockVMROM.Thm54.OptimizedComputeOverlay
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework Nock.Framework.Reify

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

/-! ## 1. A-free restored sources at an env reading the honest row -/

/-- The three hosted child-state tags of an overlay. -/
def ovTag {L : Type} (ov : SampledOverlayValues L) : Fin 3 → L
  | 0 => ov.sf1_st
  | 1 => ov.sf2_st
  | 2 => ov.sf3_st

/-- The hosted tags of `honestOverlay tg` are `tg`. -/
theorem honestOverlay_tags {L : Type} [Field L] (tg : Fin 3 → L) (pub : Pub L) (k : Fin 3) :
    ovTag (honestOverlay tg pub) k = tg k := by
  fin_cases k <;> rfl

section Src
variable {F L : Type} [Field F] [Field L] [Fintype L] [DecidableEq L]

/-- `sourcePubAtR curReader` reads only trace columns `< 67`. -/
theorem sourcePubAtR_cur_eval_congr67 {env env' : Env L}
    (h : ∀ j, j < 67 → env.trace j = env'.trace j) (st : State) (role coord : ℕ)
    (hr : role < 12) (hc : coord < 3) :
    (sourcePubAtR curReader st role coord).eval env =
      (sourcePubAtR curReader st role coord).eval env' := by
  cases st <;>
    simp only [sourcePubAtR, restoredAFieldR, restoredBFieldR, restoredIOHostFieldR,
      restoredDenomHostFieldR, pubFPR, decFPR, curReader, overlayANat, overlayBNat, ext0] <;>
    split_ifs <;> (try simp_all [Expr.eval]) <;> (try split_ifs) <;> (try simp_all [Expr.eval]) <;> (try apply h) <;> omega

/-- At a one-hot env the semantic public is the restored source of the active state. -/
theorem semanticPub_eval_eq_sourcePubAt (env : Env L) (active : State)
    (hsel : ∀ st, env.trace (Nock.Reified.opCol st) = if st = active then 1 else 0) (r c : ℕ) :
    (semanticPub .traceCur r c).eval env = (sourcePubAt .traceCur active r c).eval env := by
  unfold semanticPub
  split_ifs with h
  · exact OptimizedComputeSameExecution.restoredPub_eval_of_oneHot env active hsel r c
  · cases active <;>
      simp only [sourcePubAt, overlayANat, overlayBNat] <;>
      split_ifs <;> (try simp_all) <;> (try split_ifs) <;> (try simp_all) <;> first | rfl | (exfalso; omega)

/-- **A `Row309Reads` env agreeing with `E` below column `67`.**  `E` carries the one-hot selectors of
`pub.state` and the public/dec roles `0..53` of the un-hosted row of `(pub, dec, ex, ov)`; the dead roles
`54..57` (columns `67..70`) and challenges `0`, `5` are filled by the honest row / inputs. -/
theorem exists_reads_env (inp : Inputs L) (pub : Pub L) (dec : Dec L) (ex : Extra L)
    (ov : SampledOverlayValues L) (E : Env L)
    (hsel : ∀ st, E.trace (Nock.Reified.opCol st) = if st = pub.state then 1 else 0)
    (hext : ∀ j : Fin 54, E.trace (13 + (j : ℕ)) =
      coreExtensionValue (row309 (F := F) pub dec ex ov) ⟨j, by omega⟩) :
    ∃ E' : Env L, (∀ j, j < 67 → E.trace j = E'.trace j) ∧
      Row309Reads (F := F) E' inp pub dec ex ov := by
  let E' : Env L :=
    { trace := fun c => if h : 67 ≤ c ∧ c < 71 then
        coreExtensionValue (row309 (F := F) pub dec ex ov) ⟨c - 13, by omega⟩ else E.trace c
      traceNext := E.traceNext
      chal := fun s => if s = 0 then inp.α else if s = 5 then inp.z⁻¹ else E.chal s
      pub := E.pub }
  have hsel' : ∀ st, E'.trace (Nock.Reified.opCol st) = if st = pub.state then 1 else 0 := by
    intro st
    have hlt : Nock.Reified.opCol st < 11 := by
      rw [opCol_eq_stateIndex]; exact (stateIndex st).isLt
    have : ¬ (67 ≤ Nock.Reified.opCol st ∧ Nock.Reified.opCol st < 71) := by omega
    simp only [E', dif_neg this]
    exact hsel st
  refine ⟨E', fun j hj => by
      have : ¬ (67 ≤ j ∧ j < 71) := by omega
      simp only [E', dif_neg this], ?_⟩
  refine ⟨hsel', ?_, by simp [E'], by simp [E']⟩
  intro j
  by_cases hj : (j : ℕ) < 54
  · have h1 : ¬ (67 ≤ 13 + (j : ℕ) ∧ 13 + (j : ℕ) < 71) := by omega
    simp only [E', dif_neg h1]
    exact hext ⟨j, hj⟩
  · have h1 : 67 ≤ 13 + (j : ℕ) ∧ 13 + (j : ℕ) < 71 := by have := j.isLt; omega
    simp only [E', dif_pos h1]
    have hj13 : (⟨13 + (j : ℕ) - 13, by omega⟩ : Fin 58) = j := Fin.ext (by simp only []; omega)
    rw [hj13]

/-- **The restored sources at an env reading the honest row** (`V_comp` at the row). -/
theorem curSrc_of_reads (inp : Inputs L) (pub : Pub L) (dec : Dec L) (ex : Extra L)
    (ov : SampledOverlayValues L) (E : Env L) (hv : Vcomp inp pub dec)
    (hsel : ∀ st, E.trace (Nock.Reified.opCol st) = if st = pub.state then 1 else 0)
    (hext : ∀ j : Fin 54, E.trace (13 + (j : ℕ)) =
      coreExtensionValue (row309 (F := F) pub dec ex ov) ⟨j, by omega⟩)
    (role c : ℕ) (hr : role < 12) (hc : c < 3) :
    (sourcePubAtR curReader pub.state role c).eval E =
      fpCoordinate (pubFingerprint pub ⟨role, hr⟩) ⟨c, hc⟩ := by
  obtain ⟨E', hagree, hR⟩ := exists_reads_env (F := F) inp pub dec ex ov E hsel hext
  rw [sourcePubAtR_cur_eval_congr67 hagree _ role c hr hc, sourcePubAtR_cur,
    ← semanticPub_eval_eq_sourcePubAt E' pub.state hR.sel]
  exact hR.semPubNat_value hv role c hr hc

/-- **The hosted child tags at an env reading the honest row**: `childTagHost curReader` reads the
overlay's `sf1_st / sf2_st / sf3_st` (role-A coordinate `2`, role-B coordinates `0/1`). -/
theorem curTag_of_reads (inp : Inputs L) (pub : Pub L) (dec : Dec L) (ex : Extra L)
    (ov : SampledOverlayValues L) (E : Env L)
    (hsel : ∀ st, E.trace (Nock.Reified.opCol st) = if st = pub.state then 1 else 0)
    (hext : ∀ j : Fin 54, E.trace (13 + (j : ℕ)) =
      coreExtensionValue (row309 (F := F) pub dec ex ov) ⟨j, by omega⟩) (k : Fin 3) :
    (childTagHost curReader pub.state k).eval E =
      ovTag ov k := by
  obtain ⟨E', hagree, hR⟩ := exists_reads_env (F := F) inp pub dec ex ov E hsel hext
  have key : ∀ (r c : ℕ) (hr : r < 12) (hc : c < 3), r < 12 →
      (pubFPR curReader r c).eval E = (pubFP .traceCur r c).eval E' := by
    intro r c hr hc _
    simp only [pubFPR, pubFP, curReader, ext0, Expr.eval]
    exact hagree _ (by omega)
  have hP := hR.pubFPNat
  fin_cases k <;> cases hs : pub.state <;>
    simp only [childTagHost, overlayANat, overlayBNat] <;>
    rw [key _ _ (by decide) (by decide) (by decide), hP _ _ (by decide) (by decide)] <;>
    simp [sampledEncodeExtension309, sampledEncodeExtension, overlayRoleA, overlayRoleB,
      sampledOverlayA, fpCoordinate, ovTag, hs]

end Src

/-! ## 2. At the honest tower env -/

section Fill
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- The one-hot state selectors of a `genRowVals` row, as the source reads them. -/
theorem genRowVals_sel (pub : Pub (Quad (algebraMap F K δ))) (dec : Dec (Quad (algebraMap F K δ)))
    (ex : Extra (Quad (algebraMap F K δ))) (i n : ℕ)
    (wc wa wln winv r58 r59 : Quad (algebraMap F K δ)) (vcl : ℕ → F) (tg : Fin 3 → Quad (algebraMap F K δ)) (st : State) :
    (genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg).base
        ⟨Nock.Reified.opCol st, by
          have := opCol_eq_stateIndex st; have := (stateIndex st).isLt; omega⟩ =
      if st = pub.state then 1 else 0 := by
  have hlt : Nock.Reified.opCol st < 11 := by
    rw [opCol_eq_stateIndex]; exact (stateIndex st).isLt
  simp only [genRowVals, hlt, if_true]
  by_cases hs : st = pub.state <;> simp [hs, opCol_eq_stateIndex, stateIndex_eq_iff]

/-- The selector and role `0..53` reads of the SUCCESSOR row of the honest tower env (`hFn`). -/
theorem next_hyps (b : Basis (Fin 3) F K)
    (pub : Pub (Quad (algebraMap F K δ))) (dec : Dec (Quad (algebraMap F K δ)))
    (ex : Extra (Quad (algebraMap F K δ))) (i n : ℕ)
    (wc wa wln winv r58 r59 : Quad (algebraMap F K δ)) (vcl : ℕ → F) (tg : Fin 3 → Quad (algebraMap F K δ)) (eF : Env F)
    (hFn : ∀ c, SrcRead c → eF.traceNext c = srcColT b
      (genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg) c)
    (h58 : Quad.im _ r58 = 0) (h61 : Quad.im _ wln = 0) (h62 : Quad.im _ winv = 0) :
    (∀ st, (shiftNext (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv).trace
        (Nock.Reified.opCol st) = if st = pub.state then 1 else 0) ∧
    (∀ j : Fin 54, (shiftNext (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv).trace
        (13 + (j : ℕ)) = coreExtensionValue (row309 (F := F) pub dec ex (honestOverlay tg pub)) ⟨j, by omega⟩) := by
  set v := genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg with hvdef
  refine ⟨?_, ?_⟩
  · intro st
    have hlt : Nock.Reified.opCol st < 11 := by
      rw [opCol_eq_stateIndex]; exact (stateIndex st).isLt
    have a1 : Nock.Reified.opCol st ≠ 303 := by omega
    have a2 : Nock.Reified.opCol st ≠ 306 := by omega
    show (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv.traceNext (Nock.Reified.opCol st) = _
    simp only [Env309.toSourceEnv, a1, a2, if_false, CorrectedFinalTypedEnv.toSourceEnv,
      show Nock.Reified.opCol st < 13 by omega, dif_pos]
    rw [towerEnv309_baseNext_of_src b v eF hFn, hvdef, genRowVals_sel]
    split_ifs <;> simp
  · intro j
    have h1 : (13 + (j : ℕ)) ≠ 303 := by omega
    have h2 : (13 + (j : ℕ)) ≠ 306 := by omega
    have h3 : ¬ (13 + (j : ℕ) < 13) := by omega
    have h4 : 13 + (j : ℕ) < 76 := by omega
    show (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv.traceNext (13 + (j : ℕ)) = _
    simp only [Env309.toSourceEnv, h1, h2, if_false, CorrectedFinalTypedEnv.toSourceEnv, h3, h4,
      dif_neg, dif_pos, not_false_eq_true]
    have hj : 13 + (j : ℕ) - 13 = j := by omega
    have e := towerEnv309_extNext_of_src b v eF hFn ⟨j, by omega⟩
      (genRowVals_imZero pub dec ex i n wc wa wln winv r58 r59 vcl tg h58 h61 h62 ⟨j, by omega⟩
        (by simp; omega) (by simp; omega))
    have e2 := genRowVals_ext_lt pub dec ex i n wc wa wln winv r58 r59 vcl tg j (by omega)
    simp only [hj]
    exact e.trans e2

/-- The selector and role `0..53` reads of the CURRENT row of the honest tower env (`hF`). -/
theorem first_hyps (b : Basis (Fin 3) F K)
    (pub : Pub (Quad (algebraMap F K δ))) (dec : Dec (Quad (algebraMap F K δ)))
    (ex : Extra (Quad (algebraMap F K δ))) (i n : ℕ)
    (wc wa wln winv r58 r59 : Quad (algebraMap F K δ)) (vcl : ℕ → F) (tg : Fin 3 → Quad (algebraMap F K δ)) (eF : Env F)
    (hF : ∀ c, SrcRead c → eF.trace c = srcColT b
      (genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg) c)
    (h58 : Quad.im _ r58 = 0) (h61 : Quad.im _ wln = 0) (h62 : Quad.im _ winv = 0) :
    (∀ st, (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv.trace
        (Nock.Reified.opCol st) = if st = pub.state then 1 else 0) ∧
    (∀ j : Fin 54, (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv.trace
        (13 + (j : ℕ)) = coreExtensionValue (row309 (F := F) pub dec ex (honestOverlay tg pub)) ⟨j, by omega⟩) := by
  set v := genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg with hvdef
  refine ⟨?_, ?_⟩
  · intro st
    have hlt : Nock.Reified.opCol st < 11 := by
      rw [opCol_eq_stateIndex]; exact (stateIndex st).isLt
    have a1 : Nock.Reified.opCol st ≠ 303 := by omega
    have a2 : Nock.Reified.opCol st ≠ 306 := by omega
    simp only [Env309.toSourceEnv, a1, a2, if_false, CorrectedFinalTypedEnv.toSourceEnv,
      show Nock.Reified.opCol st < 13 by omega, dif_pos]
    rw [towerEnv309_base_of_src b v eF hF, hvdef, genRowVals_sel]
    split_ifs <;> simp
  · intro j
    have h1 : (13 + (j : ℕ)) ≠ 303 := by omega
    have h2 : (13 + (j : ℕ)) ≠ 306 := by omega
    have h3 : ¬ (13 + (j : ℕ) < 13) := by omega
    have h4 : 13 + (j : ℕ) < 76 := by omega
    simp only [Env309.toSourceEnv, h1, h2, if_false, CorrectedFinalTypedEnv.toSourceEnv, h3, h4,
      dif_neg, dif_pos, not_false_eq_true]
    have hj : 13 + (j : ℕ) - 13 = j := by omega
    have e := towerEnv309_ext_of_src b v eF hF ⟨j, by omega⟩
      (genRowVals_imZero pub dec ex i n wc wa wln winv r58 r59 vcl tg h58 h61 h62 ⟨j, by omega⟩
        (by simp; omega) (by simp; omega))
    have e2 := genRowVals_ext_lt pub dec ex i n wc wa wln winv r58 r59 vcl tg j (by omega)
    simp only [hj]
    exact e.trans e2

/-- **`NextReads.src` at the honest tower env.**  With the next row filled by `genRowVals` of its
`(pub, dec, ex)` (`hFn`) and `V_comp` there, the restored sources read at `shiftNext` are the row's
fingerprint coordinates.  (Roles `0..53` only; the dead roles `54/55` are not read.) -/
theorem nextSrc_of_fill (b : Basis (Fin 3) F K)
    (pub : Pub (Quad (algebraMap F K δ))) (dec : Dec (Quad (algebraMap F K δ)))
    (ex : Extra (Quad (algebraMap F K δ))) (i n : ℕ)
    (wc wa wln winv r58 r59 : Quad (algebraMap F K δ)) (vcl : ℕ → F) (tg : Fin 3 → Quad (algebraMap F K δ)) (eF : Env F)
    (inp : Inputs (Quad (algebraMap F K δ)))
    (hFn : ∀ c, SrcRead c → eF.traceNext c = srcColT b
      (genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg) c)
    (h58 : Quad.im _ r58 = 0) (h61 : Quad.im _ wln = 0) (h62 : Quad.im _ winv = 0)
    (hv : Vcomp inp pub dec) (role c : ℕ) (hr : role < 12) (hc : c < 3) :
    (sourcePubAtR curReader pub.state role c).eval
        (shiftNext (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv) =
      fpCoordinate (pubFingerprint pub ⟨role, hr⟩) ⟨c, hc⟩ := by
  obtain ⟨hs, he⟩ := next_hyps b pub dec ex i n wc wa wln winv r58 r59 vcl tg eF hFn h58 h61 h62
  exact curSrc_of_reads (F := F) inp pub dec ex (honestOverlay tg pub) _ hv hs he role c hr hc

/-- **`FirstReads.src` at the honest tower env**: the same at the CURRENT row (the first row, `hF`). -/
theorem firstSrc_of_fill (b : Basis (Fin 3) F K)
    (pub : Pub (Quad (algebraMap F K δ))) (dec : Dec (Quad (algebraMap F K δ)))
    (ex : Extra (Quad (algebraMap F K δ))) (i n : ℕ)
    (wc wa wln winv r58 r59 : Quad (algebraMap F K δ)) (vcl : ℕ → F) (tg : Fin 3 → Quad (algebraMap F K δ)) (eF : Env F)
    (inp : Inputs (Quad (algebraMap F K δ)))
    (hF : ∀ c, SrcRead c → eF.trace c = srcColT b
      (genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg) c)
    (h58 : Quad.im _ r58 = 0) (h61 : Quad.im _ wln = 0) (h62 : Quad.im _ winv = 0)
    (hv : Vcomp inp pub dec) (role c : ℕ) (hr : role < 12) (hc : c < 3) :
    (sourcePubAtR curReader pub.state role c).eval
        (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv =
      fpCoordinate (pubFingerprint pub ⟨role, hr⟩) ⟨c, hc⟩ := by
  obtain ⟨hs, he⟩ := first_hyps b pub dec ex i n wc wa wln winv r58 r59 vcl tg eF hF h58 h61 h62
  exact curSrc_of_reads (F := F) inp pub dec ex (honestOverlay tg pub) _ hv hs he role c hr hc

/-- **The hosted child tags at the successor row of the honest tower env are the overlay's**:
`childTagHost curReader` at `shiftNext` reads `(honestOverlay tg pub).sf{k+1}_st`. -/
theorem nextTag_of_fill (b : Basis (Fin 3) F K)
    (pub : Pub (Quad (algebraMap F K δ))) (dec : Dec (Quad (algebraMap F K δ)))
    (ex : Extra (Quad (algebraMap F K δ))) (i n : ℕ)
    (wc wa wln winv r58 r59 : Quad (algebraMap F K δ)) (vcl : ℕ → F) (tg : Fin 3 → Quad (algebraMap F K δ)) (eF : Env F)
    (inp : Inputs (Quad (algebraMap F K δ)))
    (hFn : ∀ c, SrcRead c → eF.traceNext c = srcColT b
      (genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg) c)
    (h58 : Quad.im _ r58 = 0) (h61 : Quad.im _ wln = 0) (h62 : Quad.im _ winv = 0) (k : Fin 3) :
    (childTagHost curReader pub.state k).eval
        (shiftNext (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv) =
      ovTag (honestOverlay tg pub) k := by
  obtain ⟨hs, he⟩ := next_hyps b pub dec ex i n wc wa wln winv r58 r59 vcl tg eF hFn h58 h61 h62
  exact curTag_of_reads (F := F) inp pub dec ex (honestOverlay tg pub) _ hs he k

/-- The same at the current (first) row. -/
theorem firstTag_of_fill (b : Basis (Fin 3) F K)
    (pub : Pub (Quad (algebraMap F K δ))) (dec : Dec (Quad (algebraMap F K δ)))
    (ex : Extra (Quad (algebraMap F K δ))) (i n : ℕ)
    (wc wa wln winv r58 r59 : Quad (algebraMap F K δ)) (vcl : ℕ → F) (tg : Fin 3 → Quad (algebraMap F K δ)) (eF : Env F)
    (inp : Inputs (Quad (algebraMap F K δ)))
    (hF : ∀ c, SrcRead c → eF.trace c = srcColT b
      (genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg) c)
    (h58 : Quad.im _ r58 = 0) (h61 : Quad.im _ wln = 0) (h62 : Quad.im _ winv = 0) (k : Fin 3) :
    (childTagHost curReader pub.state k).eval
        (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv =
      ovTag (honestOverlay tg pub) k := by
  obtain ⟨hs, he⟩ := first_hyps b pub dec ex i n wc wa wln winv r58 r59 vcl tg eF hF h58 h61 h62
  exact curTag_of_reads (F := F) inp pub dec ex (honestOverlay tg pub) _ hs he k

/-- **`NextReads.tag` discharged (C1g)**: with the overlay tag vector `tg k = childStateTagCol W (j+1) k`
(the deployed `overlayAt` value), the hosted tag read at the successor row IS `childStateTagCol W (j+1) k`. -/
theorem nextTag_honest (b : Basis (Fin 3) F K)
    (pub : Pub (Quad (algebraMap F K δ))) (dec : Dec (Quad (algebraMap F K δ)))
    (ex : Extra (Quad (algebraMap F K δ))) (i n : ℕ)
    (wc wa wln winv r58 r59 : Quad (algebraMap F K δ)) (vcl : ℕ → F) (eF : Env F)
    (inp : Inputs (Quad (algebraMap F K δ)))
    (W : List (Walk.NTree (State × DTcomp (Quad (algebraMap F K δ)))))
    (hFn : ∀ c, SrcRead c → eF.traceNext c = srcColT b
      (genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl (fun k => childStateTagCol W (i + 1) k)) c)
    (h58 : Quad.im _ r58 = 0) (h61 : Quad.im _ wln = 0) (h62 : Quad.im _ winv = 0) (k : Fin 3) :
    (childTagHost curReader pub.state k).eval
        (shiftNext (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv) =
      childStateTagCol W (i + 1) k := by
  rw [nextTag_of_fill b pub dec ex i n wc wa wln winv r58 r59 vcl _ eF inp hFn h58 h61 h62 k,
    honestOverlay_tags]

/-- **`FirstReads.tag` discharged (C1g)**: with `tg k = childStateTagCol W 1 k` at row `0`. -/
theorem firstTag_honest (b : Basis (Fin 3) F K)
    (pub : Pub (Quad (algebraMap F K δ))) (dec : Dec (Quad (algebraMap F K δ)))
    (ex : Extra (Quad (algebraMap F K δ))) (n : ℕ)
    (wc wa wln winv r58 r59 : Quad (algebraMap F K δ)) (vcl : ℕ → F) (eF : Env F)
    (inp : Inputs (Quad (algebraMap F K δ)))
    (W : List (Walk.NTree (State × DTcomp (Quad (algebraMap F K δ)))))
    (hF : ∀ c, SrcRead c → eF.trace c = srcColT b
      (genRowVals pub dec ex 0 n wc wa wln winv r58 r59 vcl (fun k => childStateTagCol W 1 k)) c)
    (h58 : Quad.im _ r58 = 0) (h61 : Quad.im _ wln = 0) (h62 : Quad.im _ winv = 0) (k : Fin 3) :
    (childTagHost curReader pub.state k).eval
        (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv =
      childStateTagCol W 1 k := by
  rw [firstTag_of_fill b pub dec ex 0 n wc wa wln winv r58 r59 vcl _ eF inp hF h58 h61 h62 k,
    honestOverlay_tags]

/-- **`FirstReads.sel`**: the first-row masks `20 + opCol` of the package publics (`pubCFT_bank`). -/
theorem firstSel_of_bank (b : Basis (Fin 3) F K) (eF : Env F) (s0 : ℕ) (st0 : State) (hs0 : s0 = (stateIndex st0 : ℕ))
    (hbank : ∀ j, j < 11 → eF.pub (20 + j) = if j = s0 then 1 else 0) (st : State) :
    (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv.pub (20 + Nock.Reified.opCol st) =
      if st = st0 then 1 else 0 := by
  have hlt : Nock.Reified.opCol st < 11 := by
    rw [opCol_eq_stateIndex]; exact (stateIndex st).isLt
  have h1 : ¬ (20 + Nock.Reified.opCol st < 3) := by omega
  have h2 : 20 ≤ 20 + Nock.Reified.opCol st ∧ 20 + Nock.Reified.opCol st < 42 := by omega
  simp only [Env309.toSourceEnv, CorrectedFinalTypedEnv.toSourceEnv, h1, h2, dif_neg, dif_pos,
    not_false_eq_true]
  show algebraMap F _ (eF.pub (20 + (20 + Nock.Reified.opCol st - 20))) = _
  rw [show 20 + Nock.Reified.opCol st - 20 = Nock.Reified.opCol st by omega,
    hbank _ hlt, opCol_eq_stateIndex, hs0]
  by_cases hs : st = st0 <;> simp [hs, stateIndex_eq_iff]

end Fill

/-! ## 3. -/

section TagStop
open Nock.NockVMROM.Thm54.TraceGen
variable {L : Type} [Field L]

/-- The generator's rendered `Pub` never sets `sf1_st / sf2_st / sf3_st` (they stay `none`). -/
theorem renderNode_sf_st_none (z α : L) (g : GenComputeRow L) :
    (renderNode z α g).row.2.2.1.sf1_st = none ∧ (renderNode z α g).row.2.2.1.sf2_st = none ∧
      (renderNode z α g).row.2.2.1.sf3_st = none := by
  unfold renderNode
  cases g.skel.state <;>
    simp [renderOp0Row, renderOp1Row, renderOp2Row, renderOp3Row, renderOp4Row,
      renderOp5Row, renderOp6Row, renderOp7Row, renderOp8Row, renderOp9Row, renderConsRow]



/-- A live child's tag is never `nullStateTag` (char > 10). -/
theorem stateTag_ne_null (hchar : ∀ n : ℕ, 0 < n → n ≤ 10 → (n : L) ≠ 0) (st : State) :
    (stateTagField st : L) ≠ (nullStateTag : L) := by
  obtain ⟨t, ht11, ht10, ht⟩ : ∃ t : ℕ, t ≤ 11 ∧ t ≠ 10 ∧ (stateTagField st : L) = (t : L) := by
    cases st
    · exact ⟨0, by norm_num, by norm_num, by simp [stateTagField]⟩
    · exact ⟨1, by norm_num, by norm_num, by simp [stateTagField]⟩
    · exact ⟨2, by norm_num, by norm_num, by simp [stateTagField]⟩
    · exact ⟨3, by norm_num, by norm_num, by simp [stateTagField]⟩
    · exact ⟨4, by norm_num, by norm_num, by simp [stateTagField]⟩
    · exact ⟨5, by norm_num, by norm_num, by simp [stateTagField]⟩
    · exact ⟨6, by norm_num, by norm_num, by simp [stateTagField]⟩
    · exact ⟨7, by norm_num, by norm_num, by simp [stateTagField]⟩
    · exact ⟨8, by norm_num, by norm_num, by simp [stateTagField]⟩
    · exact ⟨9, by norm_num, by norm_num, by simp [stateTagField]⟩
    · exact ⟨11, by norm_num, by norm_num, by simp [stateTagField]⟩
  intro h
  rw [ht] at h
  have h10 : (nullStateTag : L) = ((10 : ℕ) : L) := rfl
  rw [h10] at h
  by_cases hlt : t < 10
  · apply hchar (10 - t) (by omega) (by omega)
    rw [Nat.cast_sub hlt.le, ← h]; simp
  · have : t = 11 := by omega
    subst this
    apply hchar 1 (by norm_num) (by norm_num)
    have : ((11 : ℕ) : L) - ((10 : ℕ) : L) = 0 := by rw [h]; simp
    push_cast at this ⊢; linear_combination this

/-- **NC (the tag mismatch).**  At a generator row with a live child `k` in the BFS walk `W`, the hosted tag
of `honestOverlay` (`nullStateTag`) is NOT the walk's `childStateTagCol` (the child's opcode tag).  Hence
`NextReads.tag` / `FirstReads.tag` are FALSE at `genRowVals` as defined; the overlay must host
`childStateTagCol W (i+1) k` (as the deployed `overlayAt` does). -/
theorem honestOverlay_tag_ne_childStateTagCol (hchar : ∀ n : ℕ, 0 < n → n ≤ 10 → (n : L) ≠ 0)
    (z α : L) (g : GenComputeRow L) (W : List (Walk.NTree (State × DTcomp L))) (i : ℕ) (k : Fin 3)
    (c : Walk.NTree (State × DTcomp L))
    (hc : ((W[i - 1]?).bind fun t => t.children[(k : ℕ)]?) = some c) :
    ovTag (honestOverlay (fun _ => (nullStateTag : L)) (renderNode z α g).row.2.2.1) k ≠
      childStateTagCol W i k := by
  rw [honestOverlay_tags]
  unfold childStateTagCol
  rw [hc]
  exact fun h => stateTag_ne_null hchar _ h.symm

end TagStop

/-! ## 4. The root label (`hroot`) and the BFS-row `Pub` link -/

section Root
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.ComputeWalkSeed Nock.Walk
variable {L : Type} [Field L]

theorem bfsAssign_forest_length (u : NTree (GenComputeRow L)) :
    (bfsForest [bfsAssign u]).length = (bfsForest [u]).length := by
  have h := congrArg List.length (bfsAssign_bfsForest_labels u)
  simpa using h

/-- **`D.pubAt i` is C1c's BFS row**: the `Pub` of BFS row `i` of the generator's walk tree is
`(renderNode z α (bfsLabelAt (airReorder t) (i+1))).row.2.2.1`, the row `gen_vcomp_wf` constrains. -/
theorem genWalk_bfsPubAt (z α a b c : L) (t : NTree (GenComputeRow L)) (i : ℕ)
    (hi : i < (bfsForest [airReorder t]).length) :
    bfsPubAt (genWalkRoot z α a b c t) i =
      (renderNode z α (bfsLabelAt (airReorder t) (i + 1))).row.2.2.1 := by
  have hlen : i < (bfsForest [bfsAssign (airReorder t)]).length := by
    rw [bfsAssign_forest_length]; exact hi
  have hlen' : i < (bfsForest [genWalkRoot z α a b c t]).length := by
    unfold genWalkRoot
    rw [bfsForest_mapNTree_singleton, List.length_map]; exact hlen
  unfold bfsPubAt
  rw [dif_pos hlen']
  have e1 : (bfsForest [genWalkRoot z α a b c t])[i] =
      mapNTree ((setRowCoins a b c) ∘ GenComputeRow.row ∘ renderNode z α)
        ((bfsForest [bfsAssign (airReorder t)])[i]'hlen) := by
    unfold genWalkRoot
    simp only [bfsForest_mapNTree_singleton, List.getElem_map]
  have e2 := congrArg (fun l => l[i]?) (bfsAssign_bfsForest_labels (airReorder t))
  have hr : i < (List.range' 1 (bfsForest [airReorder t]).length).length := by simpa using hi
  simp only [List.getElem?_map, List.getElem?_eq_getElem hlen, Option.map_some,
    List.getElem?_eq_getElem hr, List.getElem_range'] at e2
  rw [e1, mapNTree_label]
  simp only [Function.comp]
  have e3 : ((bfsForest [bfsAssign (airReorder t)])[i]'hlen).label =
      bfsLabelAt (airReorder t) (i + 1) := by
    have := Option.some.inj e2
    rw [this]; congr 1; omega
  rw [e3]
  rfl

/-- **The generator's root `Pub` is the claim's** (`BindsAt.root_bindings` at the generator): the root
row of the walk tree carries the root state of the formula and the `enc z` fingerprints of
`(subject, formula, result)`. -/
theorem genWalk_root_pub (z α a b c : L) {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow L)} {result : Noun}
    (h : genComputeSkeleton (K := L) fuel subject formula = .ok (t, result)) :
    (genWalkRoot z α a b c t).label.2.2.1.state = rootStateOfFormula formula ∧
      (genWalkRoot z α a b c t).label.2.2.1.s = GlobalCarryRecognizer.enc z subject ∧
      (genWalkRoot z α a b c t).label.2.2.1.f = GlobalCarryRecognizer.enc z formula ∧
      (genWalkRoot z α a b c t).label.2.2.1.e = GlobalCarryRecognizer.enc z result := by
  have hskel : (bfsAssign (airReorder t)).label.skel = t.label.skel := by
    rw [bfsAssign_label_skel, airReorder_label]
  obtain ⟨hs, hf, he⟩ := genComputeSkeleton_root_sfe_pair (p := (t, result)) h
  have hst := genComputeSkeleton_root_state fuel subject formula t result h
  simp only at hs hf he
  set g := (bfsAssign (airReorder t)).label with hg
  have hlab : (genWalkRoot z α a b c t).label.2.2.1 = (renderNode z α g).row.2.2.1 := by
    unfold genWalkRoot; rw [mapNTree_label]; rfl
  rw [hlab]
  obtain ⟨e1, e2, e3⟩ := renderNode_sfe z α g
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← renderNode_state_agree', renderNode_state, hskel, hst]
  · rw [e1, hskel, hs, encC_eq]
  · rw [e2, hskel, hf, encC_eq]
  · rw [e3, hskel, he, encC_eq]

/-- **`hroot`**: the walk's first-row label vector is the claim's at `z` (the claim being the generator's
`(subject, formula, result)`). -/
theorem genHonestWalk_hroot (z αr a b c : L) {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow L)} {result : Noun}
    (h : genComputeSkeleton (K := L) fuel subject formula = .ok (t, result))
    (D : HonestWalk L) (hD : D.root = genWalkRoot z αr a b c t) (claim : P8PublicClaim)
    (hcl : claim = ⟨subject, formula, result⟩) :
    labelVecOfPub (D.pubAt 0) = claimLabelVec z claim := by
  have hpos : 0 < D.W.length := bfsForest_singleton_length_pos _
  have h0 := genHonestWalk_pubAt D 0 hpos
  have hb : bfsPubAt D.root 0 = D.root.label.2.2.1 := by
    unfold bfsPubAt
    rw [dif_pos hpos]
    simp only [HonestWalk.W, bfsForest_singleton, List.getElem_cons_zero]
  rw [h0, hb, hD]
  obtain ⟨h1, h2, h3, h4⟩ := genWalk_root_pub z αr a b c h
  subst hcl
  exact labelVecOfPub_eq_claimLabelVec _ _ _ h1 h2 h3 h4

end Root

/-! ## 5. `den′` does not read the slot-inverse columns (the fill is not circular) -/

section DenNonCircular
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP Nock.NockVMROM.Thm54.CoordinateCompiler
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- The VCL columns holding the three slot inverses, Re (`214..219`, `223..225`) and Im (`394..402`). -/
def invColT (c : ℕ) : Prop :=
  (214 ≤ c ∧ c < 220) ∨ (223 ≤ c ∧ c < 226) ∨ (394 ≤ c ∧ c < 403)

instance (c : ℕ) : Decidable (invColT c) := by unfold invColT; infer_instance

/-- A record entry reads no inverse column (a `𝕂` limb reads three raw columns, and its Im role limb). -/
def entrySafe : Entry → Prop
  | .k l => (∀ k, k < 3 → ¬ invColT (l + k)) ∧
      ∀ i, imColOfLimb l = some i → ∀ k, k < 3 → ¬ invColT (i + k)
  | .f c => ¬ invColT c

/-- Boolean check of `entrySafe`. -/
def entrySafeB : Entry → Bool
  | .k l => (List.range 3).all (fun k => !decide (invColT (l + k))) &&
      (match imColOfLimb l with
        | none => true
        | some i => (List.range 3).all (fun k => !decide (invColT (i + k))))
  | .f c => !decide (invColT c)

theorem entrySafeB_sound (e : Entry) (h : entrySafeB e = true) : entrySafe e := by
  cases e with
  | k l =>
    simp only [entrySafeB, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true',
      decide_eq_false_iff_not] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun k hk => h1 k hk, fun i hi k hk => ?_⟩
    rw [hi] at h2
    have h2' : (List.range 3).all (fun k => !decide (invColT (i + k))) = true := h2
    simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true', decide_eq_false_iff_not] at h2'
    exact h2' k hk
  | f c => simpa [entrySafeB, entrySafe] using h

/-- **The five record lists feeding `den₀′ / den₁′ / den₂′` read no inverse column** (`decide`). -/
theorem den_entries_safe :
    (∀ c, entrySafe (formulaRec c)) ∧ (∀ c, entrySafe (tailRec c)) ∧ (∀ c, entrySafe (op0PathRec c)) ∧
      (∀ c, entrySafe (ttRec c)) ∧ (∀ c, entrySafe (op9PathRec c)) := by
  have h1 : ∀ c, entrySafeB (formulaRec c) = true := by decide +kernel
  have h2 : ∀ c, entrySafeB (tailRec c) = true := by decide +kernel
  have h3 : ∀ c, entrySafeB (op0PathRec c) = true := by decide +kernel
  have h4 : ∀ c, entrySafeB (ttRec c) = true := by decide +kernel
  have h5 : ∀ c, entrySafeB (op9PathRec c) = true := by decide +kernel
  exact ⟨fun c => entrySafeB_sound _ (h1 c), fun c => entrySafeB_sound _ (h2 c),
    fun c => entrySafeB_sound _ (h3 c), fun c => entrySafeB_sound _ (h4 c),
    fun c => entrySafeB_sound _ (h5 c)⟩

theorem limbVal_congr (b : Basis (Fin 3) F K) (f g : ℕ → F) (i : ℕ)
    (h : ∀ k, k < 3 → f (i + k) = g (i + k)) : limbVal b f i = limbVal b g i := by
  unfold limbVal
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h k k.isLt]

variable (b : Basis (Fin 3) F K) (eF eF' : Env F)

theorem entryQ_val_congr (hc : ∀ c, ¬ invColT c → eF.trace c = eF'.trace c) (e : Entry)
    (he : entrySafe e) :
    Q.val δ (entryQ F e) (gatherEnv b eF) eF = Q.val δ (entryQ F e) (gatherEnv b eF') eF' := by
  cases e with
  | k l =>
    obtain ⟨h1, h2⟩ := he
    simp only [entryQ, qvar_val, kread, gatherEnv]
    congr 1
    · exact limbVal_congr b _ _ _ fun k hk => hc _ (h1 k hk)
    · cases hi : imColOfLimb l with
      | none => rfl
      | some i =>
        simp only [imVal]
        exact limbVal_congr b _ _ _ fun k hk => hc _ (h2 i hi k hk)
  | f c =>
    simp only [entryQ, qlift_val, CoeffExpr.eval]
    rw [hc c he]

theorem selSum_eval_congr (l : List ℕ) (hl : ∀ j ∈ l, eF.trace j = eF'.trace j) :
    (selSum l : CoeffExpr F).eval eF = (selSum l : CoeffExpr F).eval eF' := by
  unfold selSum
  rw [CoeffExpr.eval_sumList, CoeffExpr.eval_sumList]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  simp [selVar, CoeffExpr.eval, hl j hj]

variable {b eF eF'}

/-- **`den₀′ / den₁′ / den₂′` do not read the slot-inverse columns.**  Two raw rows agreeing off the inverse
columns (and on the challenges, and on the selector columns `0..10`) give the same three denominators at
the tower coins; so the honest fill `inv_j := den_j′⁻¹` is not circular. -/
theorem den_noncircular (hc : ∀ c, ¬ invColT c → eF.trace c = eF'.trace c) (hch : eF.chal = eF'.chal) :
    den0Q δ (gatherEnv b eF) eF = den0Q δ (gatherEnv b eF') eF' ∧
      den1Q δ (gatherEnv b eF) eF = den1Q δ (gatherEnv b eF') eF' ∧
      den2Q δ (gatherEnv b eF) eF = den2Q δ (gatherEnv b eF') eF' := by
  obtain ⟨hF, hT, hP, hTT, h9⟩ := den_entries_safe
  have hcoins : coinsQ δ (gatherEnv b eF) eF = coinsQ δ (gatherEnv b eF') eF' := by
    simp only [coinsQ, qγ, qρ, qvar_val, kread, gatherEnv, hch]
  have hrec : ∀ {m : ℕ} (r : Fin m → Entry), (∀ c, entrySafe (r c)) →
      FiniteIO.compress (coinsQ δ (gatherEnv b eF) eF) (recValQ δ (gatherEnv b eF) eF r) =
        FiniteIO.compress (coinsQ δ (gatherEnv b eF') eF') (recValQ δ (gatherEnv b eF') eF' r) := by
    intro m r hr
    rw [hcoins]
    congr 1
    funext c
    exact entryQ_val_congr δ b eF eF' hc _ (hr c)
  have hsel : ∀ l : List ℕ, (∀ j ∈ l, j < 11) →
      Q.val δ (qlift F (selSum l)) (gatherEnv b eF) eF =
        Q.val δ (qlift F (selSum l)) (gatherEnv b eF') eF' := by
    intro l hl
    rw [qlift_val, qlift_val, selSum_eval_congr eF eF' l (fun j hj => hc j (by
      have := hl j hj; unfold invColT; omega))]
  have hsv : ∀ j, j < 11 → Q.val δ (qlift F (selVar j)) (gatherEnv b eF) eF =
      Q.val δ (qlift F (selVar j)) (gatherEnv b eF') eF' := by
    intro j hj
    rw [qlift_val, qlift_val]
    simp only [selVar, CoeffExpr.eval]
    rw [hc j (by unfold invColT; omega)]
  refine ⟨?_, ?_, ?_⟩
  · unfold den0Q
    rw [hcoins]
    congr 1
    funext c
    unfold recQ0
    split_ifs with h
    · exact entryQ_val_congr δ b eF eF' hc _ (hF ⟨c, h⟩)
    · rfl
  · unfold den1Q
    rw [hsv 0 (by norm_num), hsel slot1ExportSels (by decide), hrec _ hP, hrec _ hT]
  · unfold den2Q
    rw [hsv 6 (by norm_num), hsv 9 (by norm_num), hrec _ hTT, hrec _ h9]

end DenNonCircular

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
