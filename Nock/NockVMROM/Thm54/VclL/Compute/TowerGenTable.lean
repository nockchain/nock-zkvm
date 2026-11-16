import Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
import Nock.NockVMROM.Thm54.Unhosted309Codec

/-!
# The 94 table columns of an honest un-hosted (309) row, A-free

`OptimizedComputeSameExecution.exactFinalTransitionEnv_table_current` proves that the decoded
source row (through `computeSubst`) is `computeEnvFull` on all 94 table columns, but only at the
sampled assignment `A`, where it reads `V_comp` off `A.ComputeSampledObligations`.  Here the same
fact is stated for an ARBITRARY source environment that reads one row
`(pub, dec, ex, v)` in the **un-hosted 309 encoding** (`Unhosted309.sampledEncode309`: role-A
coordinates `0/1` carry the genuine fingerprint, walk count/acc live in the walk columns), with
`V_comp` as a plain hypothesis.  The bodies are the `A`-proofs with `encodedRowAt A i` replaced
by the generic row.

* `sampledRestore309_of_vcomp`: the deployed restore of the 309 encoding is the plain encoding.
* `semanticPub_row309`: the restored public fingerprints are the row's.
* **`table_row309`**: `(Env.ofSubst computeSubst env).trace j = computeEnvFull … j` for `j < 94`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.ComputeTable Nock.Reified
open Nock.NockVMROM.Thm54.OptimizedComputeCodec Nock.NockVMROM.Thm54.OptimizedComputeOverlay
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.Unhosted309

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

noncomputable section

section GenTable
variable {F K : Type} [Field F] [Field K]

/-- **The honest un-hosted row** (the deployed `13/58` row of `sampledEncode309`). -/
def row309 (pub : Pub K) (dec : Dec K) (ex : Extra K) (v : SampledOverlayValues K) : Row F K :=
  (sampledEncode309 (F := F) pub dec ex v).row

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- The deployed restore inverts the 309 encoding on every accepted row. -/
theorem sampledRestore309_of_vcomp {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    {ex : Extra K} {v : SampledOverlayValues K} (h : Vcomp inp pub dec) :
    sampledRestoreExtension (OptimizedComputeCodec.encodeBase (F := F) pub.state)
        (sampledEncodeExtension309 pub dec ex v) =
      OptimizedComputeCodec.encodeExtension pub dec ex := by
  obtain ⟨_, _, _, _, heval⟩ := h
  cases hs : pub.state <;>
    simp only [evalV, hs] at heval
  all_goals
    funext i
    rcases i with ⟨r, c⟩ | i
    · fin_cases r <;> fin_cases c <;>
        simp [sampledRestoreExtension, sampledEncodeExtension309, sampledEncodeExtension,
          restoredA, restoredB, restoredIOHost,
          restoredDenomHost, overlayRoleA, overlayRoleB, decodeState_encodeBase,
          OptimizedComputeCodec.encodeExtension, decodePubFingerprint,
          pubFingerprint, fpOfCoordinates, fpCoordinate,
          hs, sfz1, sfz2, sfz3] at heval ⊢ <;>
        aesop
    · simp [sampledRestoreExtension, sampledEncodeExtension309, sampledEncodeExtension]

variable (env : Env K) (inp : Inputs K) (pub : Pub K) (dec : Dec K) (ex : Extra K)
  (v : SampledOverlayValues K)

/-- **The honest row-read hypotheses** of a source environment: one-hot selectors at
`pub.state`, the 58 core roles of the 309 row at `13..`, and challenges `0` / `5` = `α`, `z⁻¹`. -/
structure Row309Reads : Prop where
  sel : ∀ st, env.trace (Nock.Reified.opCol st) = if st = pub.state then 1 else 0
  ext : ∀ j : Fin 58, env.trace (13 + j) = coreExtensionValue (row309 (F := F) pub dec ex v) j
  alpha : env.chal 0 = inp.α
  zinv : env.chal 5 = inp.z⁻¹

variable {env inp pub dec ex v}

theorem Row309Reads.pubFPNat (h : Row309Reads (F := F) env inp pub dec ex v)
    (r c : ℕ) (hr : r < 12) (hc : c < 3) :
    (pubFP .traceCur r c).eval env =
      sampledEncodeExtension309 pub dec ex v (.inl (⟨r, hr⟩, ⟨c, hc⟩)) := by
  let j : Fin 58 := ⟨3 * r + c, by omega⟩
  simp only [pubFP, ext0, Expr.eval]
  have hj := h.ext j
  rw [show 13 + 3 * r + c = 13 + (j : ℕ) by simp [j]; omega, hj]
  have e1 : (3 * r + c) / 3 = r := by omega
  have e2 : (3 * r + c) % 3 = c := by omega
  have h36 : 3 * r + c < 36 := by omega
  simp only [coreExtensionValue, j, h36, dif_pos, row309, sampledEncode309]
  congr 3 <;> simp [Fin.ext_iff, e1, e2]

theorem Row309Reads.decFPNat (h : Row309Reads (F := F) env inp pub dec ex v)
    (r c : ℕ) (hr : r < 6) (hc : c < 3) :
    (decFP .traceCur r c).eval env =
      fpCoordinate (decFingerprint dec ⟨r, hr⟩) ⟨c, hc⟩ := by
  let j : Fin 58 := ⟨36 + 3 * r + c, by omega⟩
  simp only [decFP, ext0, Expr.eval]
  have hj := h.ext j
  rw [show 13 + 36 + 3 * r + c = 13 + (j : ℕ) by simp [j]; omega, hj]
  have e1 : (36 + 3 * r + c - 36) / 3 = r := by omega
  have e2 : (36 + 3 * r + c - 36) % 3 = c := by omega
  have h36 : ¬ (36 + 3 * r + c < 36) := by omega
  have h54 : 36 + 3 * r + c < 54 := by omega
  simp only [coreExtensionValue, j, h36, h54, dif_neg, dif_pos, not_false_eq_true, row309,
    sampledEncode309]
  simp only [sampledEncodeExtension309, sampledEncodeExtension,
    OptimizedComputeCodec.encodeExtension]
  congr 2 <;> simp [Fin.ext_iff, e1, e2]

theorem Row309Reads.tail (h : Row309Reads (F := F) env inp pub dec ex v) (k : Fin 4) :
    env.trace (13 + 54 + k) = OptimizedComputeCodec.encodeExtension pub dec ex (.inr (.inr k)) := by
  have hj := h.ext ⟨54 + k, by omega⟩
  rw [show 13 + 54 + (k : ℕ) = 13 + ((⟨54 + k, by omega⟩ : Fin 58) : ℕ) by simp; omega, hj]
  have h36 : ¬ (54 + (k : ℕ) < 36) := by omega
  have h54 : ¬ (54 + (k : ℕ) < 54) := by omega
  simp only [coreExtensionValue, h36, h54, dif_neg, not_false_eq_true, row309, sampledEncode309,
    sampledEncodeExtension309, sampledEncodeExtension]
  congr 3
  exact Fin.ext (by simp)

theorem Row309Reads.lnPrev_eval (h : Row309Reads (F := F) env inp pub dec ex v) :
    (OptimizedComputeSubstitution.lnPrev .traceCur).eval env = pub.ln_prev := by
  have := h.tail 0
  simp only [OptimizedComputeSubstitution.lnPrev, ext0, Expr.eval]
  simpa [OptimizedComputeCodec.encodeExtension] using this

theorem Row309Reads.lnCur_eval (h : Row309Reads (F := F) env inp pub dec ex v) :
    (OptimizedComputeSubstitution.lnCur .traceCur).eval env = pub.ln := by
  have := h.tail 1
  simp only [OptimizedComputeSubstitution.lnCur, ext0, Expr.eval]
  simpa [OptimizedComputeCodec.encodeExtension] using this

theorem Row309Reads.consInv_eval (h : Row309Reads (F := F) env inp pub dec ex v) :
    (OptimizedComputeSubstitution.consInv .traceCur).eval env = ex.consInv := by
  have := h.tail 2
  simp only [OptimizedComputeSubstitution.consInv, ext0, Expr.eval]
  simpa [OptimizedComputeCodec.encodeExtension] using this

theorem Row309Reads.invGen_eval (h : Row309Reads (F := F) env inp pub dec ex v) :
    (OptimizedComputeSubstitution.invGen .traceCur).eval env = ex.invGen := by
  have := h.tail 3
  simp only [OptimizedComputeSubstitution.invGen, ext0, Expr.eval]
  simpa [OptimizedComputeCodec.encodeExtension] using this

variable [Fintype K] [DecidableEq K]

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
/-- (A-free `exactFinalTransitionEnv_semanticPub`, at the 309 encoding.) -/
theorem Row309Reads.semPub (h : Row309Reads (F := F) env inp pub dec ex v)
    (hv : Vcomp inp pub dec) (r : Fin 12) (c : Fin 3) :
    (OptimizedComputeSubstitution.semanticPub .traceCur r c).eval env =
      (sampledRestoreExtension
        (OptimizedComputeCodec.encodeBase (F := F) pub.state)
        (sampledEncodeExtension309 pub dec ex v)) (.inl (r, c)) := by
  have hrestore := sampledRestore309_of_vcomp (F := F) (ex := ex) (v := v) hv
  have hrestoreAt := congrFun hrestore (.inl (r, c))
  rw [hrestore]
  have hP := h.pubFPNat
  have hD := h.decFPNat
  simp only [OptimizedComputeSubstitution.semanticPub]
  split
  · rw [OptimizedComputeSameExecution.restoredPub_eval_of_oneHot _ _ h.sel r c]
    fin_cases r <;> fin_cases c <;>
      cases hs : pub.state <;>
      simp [sourcePubAt, restoredAField, restoredBField, restoredIOHostField,
        restoredDenomHostField, OptimizedComputeCodec.encodeExtension,
        OptimizedComputeCodec.pubFingerprint, OptimizedComputeCodec.decFingerprint,
        OptimizedComputeCodec.fpCoordinate, overlayANat, overlayBNat,
        overlayRoleA, overlayRoleB,
        sampledEncodeExtension309, sampledEncodeExtension,
        hP, hD,
        Expr.eval, Vcomp, evalV, sfz1, sfz2, sfz3, hs] at hv hrestoreAt ⊢ <;>
      aesop
  · fin_cases r <;> fin_cases c <;>
      cases hs : pub.state <;>
      simp [OptimizedComputeCodec.encodeExtension, OptimizedComputeCodec.pubFingerprint,
        OptimizedComputeCodec.fpCoordinate,
        sampledEncodeExtension309, sampledEncodeExtension, overlayRoleA, overlayRoleB,
        hP, hs] at *

theorem Row309Reads.semPub_value (h : Row309Reads (F := F) env inp pub dec ex v)
    (hv : Vcomp inp pub dec) (r : Fin 12) (c : Fin 3) :
    (OptimizedComputeSubstitution.semanticPub .traceCur r c).eval env = fpCoordinate (pubFingerprint pub r) c := by
  rw [h.semPub hv, sampledRestore309_of_vcomp (F := F) hv]
  rfl

theorem Row309Reads.semPubNat_value (h : Row309Reads (F := F) env inp pub dec ex v)
    (hv : Vcomp inp pub dec) (r c : ℕ) (hr : r < 12) (hc : c < 3) :
    (OptimizedComputeSubstitution.semanticPub .traceCur r c).eval env =
      fpCoordinate (pubFingerprint pub ⟨r, hr⟩) ⟨c, hc⟩ := by
  simpa using h.semPub_value hv ⟨r, hr⟩ ⟨c, hc⟩

theorem Row309Reads.pubFPNat_off (h : Row309Reads (F := F) env inp pub dec ex v)
    (r c : ℕ) (hr : r < 12) (hc : c < 3)
    (hoff : ¬ ((⟨r, hr⟩ : Fin 12) = overlayRoleA pub.state ∧ c = 2)) :
    (pubFP .traceCur r c).eval env =
      sampledEncodeExtension pub dec ex v (.inl (⟨r, hr⟩, ⟨c, hc⟩)) ∨
    (pubFP .traceCur r c).eval env = fpCoordinate (pubFingerprint pub ⟨r, hr⟩) ⟨c, hc⟩ := by
  rw [h.pubFPNat r c hr hc]
  simp only [sampledEncodeExtension309]
  split_ifs
  · right; rfl
  · left; rfl

theorem Row309Reads.table_pub (h : Row309Reads (F := F) env inp pub dec ex v) (hv : Vcomp inp pub dec)
    (r : Fin 12) (c : Fin 3) :
    (Env.ofSubst computeSubst env).trace (11 + 3 * (r : ℕ) + c) =
      (computeEnvFull inp (opSel pub.state) pub dec ex).trace (11 + 3 * (r : ℕ) + c) := by
  rw [show (Env.ofSubst computeSubst env).trace (11 + 3 * (r : ℕ) + c) =
      (OptimizedComputeSubstitution.semanticPub .traceCur r c).eval env by
    fin_cases r <;> fin_cases c <;>
      norm_num [Env.ofSubst, computeSubst, computeTraceSubst]]
  rw [h.semPub_value hv]
  fin_cases r <;> fin_cases c <;> rfl

theorem Row309Reads.table_dec (h : Row309Reads (F := F) env inp pub dec ex v)
    (r : Fin 6) (c : Fin 3) :
    (Env.ofSubst computeSubst env).trace (47 + 3 * (r : ℕ) + c) =
      (computeEnvFull inp (opSel pub.state) pub dec ex).trace (47 + 3 * (r : ℕ) + c) := by
  rw [show (Env.ofSubst computeSubst env).trace (47 + 3 * (r : ℕ) + c) =
      (decFP .traceCur r c).eval env by
    fin_cases r <;> fin_cases c <;>
      norm_num [Env.ofSubst, computeSubst, computeTraceSubst]]
  rw [h.decFPNat r c r.isLt c.isLt]
  fin_cases r <;> fin_cases c <;> rfl

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
/-- **(1) of DESIGN §(a), A-free**: all 94 current table columns decoded through `computeSubst`
from a source environment reading an accepted un-hosted row are `computeEnvFull` of that row.
(A-free copy of `exactFinalTransitionEnv_table_current`.) -/
theorem Row309Reads.table (h : Row309Reads (F := F) env inp pub dec ex v) (hv : Vcomp inp pub dec)
    (j : ℕ) (hj : j < 94) :
    (Env.ofSubst computeSubst env).trace j =
      (computeEnvFull inp (opSel pub.state) pub dec ex).trace j := by
  have hrecords := OptimizedComputeCodec.records_eq_expected_of_vcomp hv
  have h0 := h.sel .s0
  have h1 := h.sel .s1
  have h2 := h.sel .s2
  have h3 := h.sel .s3
  have h4 := h.sel .s4
  have h5 := h.sel .s5
  have h6 := h.sel .s6
  have h7 := h.sel .s7
  have h8 := h.sel .s8
  have h9 := h.sel .s9
  have h10 := h.sel .cons
  have hP := h.pubFPNat
  have hS := h.semPubNat_value hv
  have hD := h.decFPNat
  have hL := h.lnPrev_eval
  have hL' := h.lnCur_eval
  have hCI := h.consInv_eval
  have hIG := h.invGen_eval
  have hA := h.alpha
  have hZ := h.zinv
  by_cases h11 : j < 11
  · interval_cases j <;>
      norm_num [Env.ofSubst, computeSubst, computeTraceSubst, computeEnvFull] <;>
      simp_all [Expr.eval, Nock.Reified.opCol, opSel, eq_comm]
  by_cases h47 : j < 47
  · let r : Fin 12 := ⟨(j - 11) / 3, by omega⟩
    let c : Fin 3 := ⟨(j - 11) % 3, Nat.mod_lt _ (by omega)⟩
    have hidx : j = 11 + 3 * (r : ℕ) + c := by
      have hdiv := Nat.mod_add_div (j - 11) 3
      dsimp [r, c]
      omega
    rw [hidx]
    exact h.table_pub hv r c
  by_cases h65 : j < 65
  · let r : Fin 6 := ⟨(j - 47) / 3, by omega⟩
    let c : Fin 3 := ⟨(j - 47) % 3, Nat.mod_lt _ (by omega)⟩
    have hidx : j = 47 + 3 * (r : ℕ) + c := by
      have hdiv := Nat.mod_add_div (j - 47) 3
      dsimp [r, c]
      omega
    rw [hidx]
    exact h.table_dec r c
  by_cases h67 : j < 67
  · interval_cases j <;>
      norm_num [Env.ofSubst, computeSubst, computeTraceSubst, computeEnvFull] <;>
      simpa [OptimizedComputeSubstitution.lnPrev, OptimizedComputeSubstitution.lnCur, ext0,
        Expr.eval] using (by first | exact hL | exact hL')
  by_cases h75 : j < 75
  · interval_cases j <;>
      norm_num [Env.ofSubst, computeSubst, computeTraceSubst, computeEnvFull] <;>
      simp [Expr.eval, hP, hS, hD, hL, hA, row309, sampledEncode309,
        sampledEncodeExtension309, sampledEncodeExtension,
        OptimizedComputeCodec.encodeExtension, OptimizedComputeCodec.pubFingerprint,
        OptimizedComputeCodec.decFingerprint,
        OptimizedComputeCodec.fpCoordinate] at hrecords ⊢ <;>
      cases hs : pub.state <;>
      (try simp [hs, overlayRoleA, overlayRoleB] at hrecords ⊢) <;>
      aesop
  by_cases h83 : j < 83
  · interval_cases j <;>
      norm_num [Env.ofSubst, computeSubst, computeTraceSubst, computeEnvFull,
        mr2Field, mr2Group] <;>
      simp [Expr.eval, hP, hS, hD, hL, hA, row309, sampledEncode309,
        sampledEncodeExtension309, sampledEncodeExtension,
        OptimizedComputeCodec.encodeExtension, OptimizedComputeCodec.pubFingerprint,
        OptimizedComputeCodec.decFingerprint,
        OptimizedComputeCodec.fpCoordinate] at hrecords ⊢ <;>
      cases hs : pub.state <;>
      simp [hs, overlayRoleA, overlayRoleB,
        OptimizedComputeCodec.expectedMr2, opSel, Nock.Reified.opCol]
        at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hrecords ⊢ <;>
      aesop
  by_cases h91 : j < 91
  · interval_cases j <;>
      norm_num [Env.ofSubst, computeSubst, computeTraceSubst, computeEnvFull,
        mr3Field, mr3Group] <;>
      simp [Expr.eval, hP, hS, hD, hL, hA, row309, sampledEncode309,
        sampledEncodeExtension309, sampledEncodeExtension,
        OptimizedComputeCodec.encodeExtension, OptimizedComputeCodec.pubFingerprint,
        OptimizedComputeCodec.decFingerprint,
        OptimizedComputeCodec.fpCoordinate] at hrecords ⊢ <;>
      cases hs : pub.state <;>
      simp [hs, overlayRoleA, overlayRoleB,
        OptimizedComputeCodec.expectedMr3, opSel, Nock.Reified.opCol]
        at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hrecords ⊢ <;>
      aesop
  interval_cases j <;>
    norm_num [Env.ofSubst, computeSubst, computeTraceSubst, computeEnvFull] <;>
    simpa [OptimizedComputeSubstitution.consInv, OptimizedComputeSubstitution.invGen, ext0,
      Expr.eval] using (by first | exact hCI | exact hIG | exact hZ)

end GenTable

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
