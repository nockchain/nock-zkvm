import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestT
import Nock.NockVMROM.Thm54.VclL.Compute.TowerRowShape

/-!
Row-level facts about the honest compute trace of the tower chip.  It shows that each role entry,
public handle and decoded field of an honest row reads back the corresponding row value
(`role_pub`, `role_dec`, `roleFP_pub`, `roleFP_dec`), that the export and path record vectors compress
to the requests `xReq` and `pReq` (`rec0_vec`, `export10_compress`, `path_vec`), and that the honest
slot inverses are reciprocals of the row denominators.  It then proves that the export side and path
side of a row sum to the stated request terms, the request shapes of every walk row (`gRow_facts`),
the row-level identities `hrowX_row` / `hrowP_row` and their versions at every honest row
(`hrowX_T`, `hrowP_T`), and that the `z1` gates hold at every honest row (`z1Gates_row`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Walk Nock.ComputeTable Nock.Reified Module
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0TowerFP Nock.NockVMROM.Thm54.VclL.Compute.LnRead Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.OptimizedComputeCodec Nock.NockVMROM.Thm54.OptimizedComputeOverlay
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace Nock.NockVMROM.Thm54.Unhosted309

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

section Roles
variable {F L : Type} [Field F] [Field L]

theorem role_pub (pub : Pub L) (dec : Dec L) (ex : Extra L) (v : SampledOverlayValues L) (k : Fin 12) (c : Fin 3)
    (hk : k = 1 ∨ (pub.state = .s0 ∧ (k = 0 ∨ k = 2)) ∨ (pub.state = .s9 ∧ (k = 5 ∨ k = 7)))
    (hi : 3 * (k : ℕ) + c < 58) :
    coreExtensionValue (row309 (F := F) pub dec ex v) ⟨3 * (k : ℕ) + c, hi⟩ =
      fpCoordinate (pubFingerprint pub k) c := by
  have h36 : 3 * (k : ℕ) + c < 36 := by omega
  have e1 : (3 * (k : ℕ) + c) / 3 = k := by omega
  have e2 : (3 * (k : ℕ) + c) % 3 = c := by omega
  have hAB : k ≠ overlayRoleA pub.state ∧ k ≠ overlayRoleB pub.state ∧ k ≠ 10 ∧ k ≠ 11 := by
    rcases hk with h | ⟨hs, h⟩ | ⟨hs, h⟩
    · subst h; cases pub.state <;> decide
    · rw [hs]; rcases h with h | h <;> subst h <;> decide
    · rw [hs]; rcases h with h | h <;> subst h <;> decide
  obtain ⟨a1, a2, a3, a4⟩ := hAB
  have core : sampledEncodeExtension309 pub dec ex v (.inl (k, c)) =
      fpCoordinate (pubFingerprint pub k) c := by
    simp only [sampledEncodeExtension309, sampledEncodeExtension, a1, a2, a3, a4, false_and, and_false,
      if_false, OptimizedComputeCodec.encodeExtension]
  simp only [coreExtensionValue, h36, dif_pos, row309, sampledEncode309]
  rw [← core]
  congr 3 <;> simp [Fin.ext_iff, e1, e2]

theorem role_dec (pub : Pub L) (dec : Dec L) (ex : Extra L) (v : SampledOverlayValues L) (k : Fin 6) (c : Fin 3)
    (hi : 36 + 3 * (k : ℕ) + c < 58) :
    coreExtensionValue (row309 (F := F) pub dec ex v) ⟨36 + 3 * (k : ℕ) + c, hi⟩ =
      fpCoordinate (decFingerprint dec k) c := by
  have h36 : ¬ (36 + 3 * (k : ℕ) + c < 36) := by omega
  have h54 : 36 + 3 * (k : ℕ) + c < 54 := by omega
  have e1 : (36 + 3 * (k : ℕ) + c - 36) / 3 = k := by omega
  have e2 : (36 + 3 * (k : ℕ) + c - 36) % 3 = c := by omega
  simp only [coreExtensionValue, h36, h54, dif_neg, dif_pos, not_false_eq_true, row309, sampledEncode309,
    sampledEncodeExtension309, sampledEncodeExtension, OptimizedComputeCodec.encodeExtension]
  congr 2 <;> exact Fin.ext (by omega)

end Roles

section EntryRole
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **A role entry of the honest row reads back the row's role value**: `Q.val (entryQ (.k (13 + 3 r)))` at the
honest row environment is `(rows i).ext r`, for every role with an Im column. -/
theorem entryQ_role_val (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)
    (hinj : Function.Injective nodes) (rows : Fin n → TowerRowVals (K := K) δ) (ω : F) (cv pv : ℕ → F)
    (i : Fin n) (r : Fin 63) (hne : fullImMap.ext r ≠ none) :
    Q.val δ (entryQ F (.k (13 + 3 * (r : ℕ))))
      (gatherEnv b (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv))
      (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv) = (rows i).ext r := by
  set E := Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv with hE
  have htr : ∀ j, j < 409 → E.trace j = vclColT b rows j i := fun j hj =>
    env_honestQT_trace b nodes hinj rows ω cv pv i (by show j < vclWidthT; simp only [vclWidthT]; omega)
  have hr63 := r.isLt
  have himk : ∀ r : Fin 63, (232 ≤ (fullImMap.ext r).getD 0 ∧ (fullImMap.ext r).getD 0 + 2 < 394 ∧
      ∀ c', fullImMap.ext r = some c' → towerM.ext r = some (c' + 95)) ∨ fullImMap.ext r = none := by
    decide +kernel
  have hre : ∀ k : Fin 3, E.trace (13 + 3 * (r : ℕ) + k) = coord b (Quad.re _ ((rows i).ext r)) k := by
    intro k
    have := k.isLt
    rw [htr _ (by omega), vclColT, if_pos (by omega), srcColT_role]
  obtain ⟨c', hc'⟩ : ∃ c', fullImMap.ext r = some c' := by
    cases hh : fullImMap.ext r with
    | none => exact absurd hh hne
    | some c' => exact ⟨c', rfl⟩
  have him : ∀ k : Fin 3, E.trace (c' + k) = coord b (Quad.im _ ((rows i).ext r)) k := by
    intro k
    rcases himk r with ⟨h1, h2, h3⟩ | h
    · have hk := k.isLt
      rw [hc'] at h1 h2
      simp only [Option.getD_some] at h1 h2
      rw [htr _ (by omega), vclColT, if_neg (by omega), if_pos (Or.inr ⟨by omega, by omega⟩),
        show c' + (k : ℕ) + 95 = (c' + 95) + (k : ℕ) by omega, srcColT_im b _ r _ (h3 c' hc') k]
    · rw [hc'] at h; exact absurd h (by simp)
  have himc : imColOfLimb (13 + 3 * (r : ℕ)) = some c' := by
    have h : 13 ≤ 13 + 3 * (r : ℕ) ∧ (13 + 3 * (r : ℕ) - 13) / 3 < 63 := ⟨by omega, by omega⟩
    simp only [imColOfLimb, dif_pos h]
    have e : (13 + 3 * (r : ℕ) - 13) / 3 = r := by omega
    have : (⟨(13 + 3 * (r : ℕ) - 13) / 3, h.2⟩ : Fin 63) = r := Fin.ext e
    rw [this, hc']
  show Q.val δ (qvar F VarKind.traceCur (13 + 3 * (r : ℕ)) (imColOfLimb (13 + 3 * (r : ℕ)))) _ E = _
  rw [qvar_val, himc]
  have r1 : kread (gatherEnv b E) VarKind.traceCur (13 + 3 * (r : ℕ)) = Quad.re _ ((rows i).ext r) := by
    simp only [kread, gatherEnv]
    exact LogUp.limbVal_eq_of_coords b _ _ _ (fun k => (hre k).symm)
  have r2 : imVal (kread (gatherEnv b E) VarKind.traceCur) (some c') = Quad.im _ ((rows i).ext r) := by
    simp only [imVal, kread, gatherEnv]
    exact LogUp.limbVal_eq_of_coords b _ _ _ (fun k => (him k).symm)
  rw [r1, r2, Quad.mk_re_im]

end EntryRole

section Records
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K) (E : Env F)

/-- The three `𝕂′` role entries at `R, R+1, R+2` of the row read the fingerprint `A`. -/
def RoleFP (R : ℕ) (A : FP (Quad (algebraMap F K δ))) : Prop :=
  ∀ c : Fin 3, Q.val δ (entryQ F (fpEntry R c)) (gatherEnv b E) E = fpCoordinate A c

variable {δ b E}

theorem recValQ_exportRec {p l r idx : ℕ} {A B C : FP (Quad (algebraMap F K δ))} {xi : Quad (algebraMap F K δ)}
    (hA : RoleFP δ b E p A) (hB : RoleFP δ b E l B) (hC : RoleFP δ b E r C)
    (hi : Q.val δ (entryQ F (.f idx)) (gatherEnv b E) E = xi) :
    recValQ δ (gatherEnv b E) E (exportRec p l r idx) =
      ![A.size, A.dyck, A.leaf, B.size, B.dyck, B.leaf, C.size, C.dyck, C.leaf, xi] := by
  funext i
  fin_cases i
  · exact hA 0
  · exact hA 1
  · exact hA 2
  · exact hB 0
  · exact hB 1
  · exact hB 2
  · exact hC 0
  · exact hC 1
  · exact hC 2
  · exact hi

theorem recValQ_pathRec {root child ax idx : ℕ} {A B : FP (Quad (algebraMap F K δ))}
    {av xi : Quad (algebraMap F K δ)}
    (hA : RoleFP δ b E root A) (hB : RoleFP δ b E child B)
    (ha : Q.val δ (entryQ F (.f ax)) (gatherEnv b E) E = av)
    (hi : Q.val δ (entryQ F (.f idx)) (gatherEnv b E) E = xi) :
    recValQ δ (gatherEnv b E) E (pathRec root child ax idx) =
      ![A.size, A.dyck, A.leaf, B.size, B.dyck, B.leaf, av, xi] := by
  funext i
  fin_cases i
  · exact hA 0
  · exact hA 1
  · exact hA 2
  · exact hB 0
  · exact hB 1
  · exact hB 2
  · exact ha
  · exact hi

variable (γ ρ : Quad (algebraMap F K δ))

/-- A width-`11` record with a trailing `0` compresses as its width-`10` prefix. -/
theorem compress11_of_last_zero (w : Fin 11 → Quad (algebraMap F K δ)) (h : w 10 = 0) :
    FiniteIO.compress (m := 11) ⟨γ, ρ⟩ w = FiniteIO.compress (m := 10) ⟨γ, ρ⟩ (fun i => w i.castSucc) := by
  simp only [FiniteIO.compress, Walk.rlc]
  rw [Fin.sum_univ_castSucc]
  have : w (Fin.last 10) = 0 := h
  rw [this, mul_zero, add_zero]
  rfl

end Records

section RowEnv
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [DecidableEq F] {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))] {hC : ℕ} {S : MemShape}
variable (V : VerifierData F K hC S) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ)) {fuel : ℕ}
  {subject formula : Noun} {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))} {result : Noun}
  (hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel subject formula = .ok (t, result))
  (accX accP : ℕ → Quad (algebraMap F K δ))

theorem rowsAcc_ext_lt (i : Fin V.N) (r : ℕ) (hr : r < 58) :
    (rowsAcc V χ αs hgen accX accP i).ext ⟨r, by omega⟩ =
      coreAt t αs (zQuad δ χ) (ιc χ ⟨8, by decide⟩) (ιc χ ⟨9, by decide⟩) (ιc χ ⟨10, by decide⟩) i ⟨r, hr⟩ := by
  simp only [rowsAcc, rowsFinal, rowFinal, rowGen]
  rw [genRowVals_ext_lt _ _ _ _ _ _ _ _ _ _ _ _ _ r hr]
  rfl

theorem rowsAcc_vcl (i : Fin V.N) (c : ℕ) :
    (rowsAcc V χ αs hgen accX accP i).vcl c =
      vclFill (δ := δ) V.basis (serT i) (axT t i) (fIdxT t i) (vIT t 1 i) (vIT t 2 i)
        (inv0F V.basis χ αs (walkT χ αs hgen) V.N (decT χ αs t) serT (axT t) (fIdxT t) (vIT t 1) (vIT t 2)
          accX accP V.computeNodes V.orbitC.ω (chalVQ7T δ V.basis χ) (pubCFT δ V (xT t) (reqT t χ) χ) i)
        (inv1F V.basis χ αs (walkT χ αs hgen) V.N (decT χ αs t) serT (axT t) (fIdxT t) (vIT t 1) (vIT t 2)
          accX accP V.computeNodes V.orbitC.ω (chalVQ7T δ V.basis χ) (pubCFT δ V (xT t) (reqT t χ) χ) i)
        (inv2F V.basis χ αs (walkT χ αs hgen) V.N (decT χ αs t) serT (axT t) (fIdxT t) (vIT t 1) (vIT t 2)
          accX accP V.computeNodes V.orbitC.ω (chalVQ7T δ V.basis χ) (pubCFT δ V (xT t) (reqT t χ) χ) i)
        (accX i) (accP i) c := rfl

theorem envAcc_eq (j : ℕ) (hj : j < V.N) :
    envAcc V χ αs hgen accX accP j =
      Reify.envOfTrace (honestQT V.basis V.computeNodes (rowsAcc V χ αs hgen accX accP) vclWidthT) V.orbitC.ω
        (V.computeNodes ⟨j, hj⟩) (chalVQ7T δ V.basis χ) (pubCFT δ V (xT t) (reqT t χ) χ) := by
  simp only [envAcc, dif_pos hj]

theorem envAcc_chal (j : ℕ) (hj : j < V.N) :
    (envAcc V χ αs hgen accX accP j).chal = chalVQ7T δ V.basis χ := by
  rw [envAcc_eq V χ αs hgen accX accP j hj]; rfl

variable (hnodes : ∀ i : Fin V.N, V.computeNodes i = V.orbitC.ω ^ (i : ℕ)) (hsize : V.N ≤ 2 ^ hC)

include hnodes hsize in
theorem envAcc_vclOnly (j : ℕ) (hj : j < V.N) (c : ℕ) (hc : 202 ≤ c ∧ (c < 208 ∨ (214 ≤ c ∧ c < 232))) :
    (envAcc V χ αs hgen accX accP j).trace c = (rowsAcc V χ αs hgen accX accP ⟨j, hj⟩).vcl c := by
  rw [envAcc_eq V χ αs hgen accX accP j hj,
    env_honestQT_trace V.basis V.computeNodes (injective_of_pow V hnodes hsize) _ _ _ _ _
      (by simp only [vclWidthT]; omega),
    vclColT_vclOnly V.basis _ _ c hc.1 hc.2]

include hnodes hsize in
theorem envAcc_entry_f (j : ℕ) (hj : j < V.N) (c : ℕ) (hc : 202 ≤ c ∧ (c < 208 ∨ (214 ≤ c ∧ c < 232))) :
    Q.val δ (entryQ F (.f c)) (gatherEnv V.basis (envAcc V χ αs hgen accX accP j)) (envAcc V χ αs hgen accX accP j) =
      liftQ δ ((rowsAcc V χ αs hgen accX accP ⟨j, hj⟩).vcl c) := by
  show Q.val δ (qlift F (.var .traceCur c)) _ _ = _
  rw [qlift_val]
  simp only [CoeffExpr.eval]
  rw [envAcc_vclOnly V χ αs hgen accX accP hnodes hsize j hj c hc]
  exact (IsScalarTower.algebraMap_apply F K _ _).symm

include hnodes hsize in
/-- **The honest `z1` column** of row `j` is `[axis = 1]` (the natural axis; `honestAx = 0` off `s0` / `s9`),
at EVERY accumulator filling. -/
theorem col_z1 (j : ℕ) (hj : j < V.N) :
    (envAcc V χ αs hgen accX accP j).trace z1Col = if honestAx (gRow t j).skel = 1 then 1 else 0 := by
  rw [envAcc_eq V χ αs hgen accX accP j hj,
    env_honestQT_trace V.basis V.computeNodes (injective_of_pow V hnodes hsize) _ _ _ _ _
      (by decide : z1Col < vclWidthT)]
  simp only [vclColT, z1Col, show ¬ (409 < 202) by omega,
    show ¬ ((208 ≤ 409 ∧ 409 < 214) ∨ (232 ≤ 409 ∧ 409 < 394)) by omega, if_false]
  rw [rowsAcc_vcl]
  exact vclFill_z1 (δ := δ) V.basis _ _ _ _ _ _ _ _ _ _

include hnodes hsize in
theorem col_axF (j : ℕ) (hj : j < V.N) :
    (envAcc V χ αs hgen accX accP j).trace axCol = ((honestAx (gRow t j).skel : ℕ) : F) := by
  rw [envAcc_vclOnly V χ αs hgen accX accP hnodes hsize j hj axCol (by unfold axCol; omega), rowsAcc_vcl]
  exact vclFill_ax (δ := δ) V.basis _ _ _ _ _ _ _ _ _ _

end RowEnv

section Render
variable {L : Type} [Field L] (z α : L) (g : GenComputeRow L)

theorem rn_pub_s : (renderNode z α g).row.2.2.1.s = encC z g.skel.subject := by
  unfold renderNode; cases g.skel.state <;> rfl
theorem rn_pub_f : (renderNode z α g).row.2.2.1.f = encC z g.skel.formula := by
  unfold renderNode; cases g.skel.state <;> rfl
theorem rn_pub_e : (renderNode z α g).row.2.2.1.e = encC z g.skel.evaluation := by
  unfold renderNode; cases g.skel.state <;> rfl
theorem rn_pub_sf1e (h : g.skel.state = .s9) :
    (renderNode z α g).row.2.2.1.sf1_e = encC z (P8Census.skeletonSubformula g.skel 0 .result) := by
  unfold renderNode; rw [h]; rfl
theorem rn_pub_sf2f (h : g.skel.state = .s9) :
    (renderNode z α g).row.2.2.1.sf2_f = encC z (P8Census.skeletonSubformula g.skel 1 .formula) := by
  unfold renderNode; rw [h]; rfl
theorem rn_dec_h : (renderNode z α g).row.2.2.2.f_h = encC z (formulaHead g.skel.formula) := by
  unfold renderNode; cases g.skel.state <;> rfl
theorem rn_dec_t_ne (h : g.skel.state ≠ .s1) :
    (renderNode z α g).row.2.2.2.f_t = encC z (formulaTail g.skel.formula) := by
  unfold renderNode
  cases hs : g.skel.state <;> first | rfl | exact absurd hs h
theorem rn_dec_t_s1 (h : g.skel.state = .s1) :
    (renderNode z α g).row.2.2.2.f_t = encC z g.skel.evaluation := by
  unfold renderNode; rw [h]; rfl
theorem rn_dec_th (h : g.skel.state = .s2 ∨ g.skel.state = .s5 ∨ g.skel.state = .s6 ∨ g.skel.state = .s7 ∨
    g.skel.state = .s8 ∨ g.skel.state = .s9) :
    (renderNode z α g).row.2.2.2.f_th = encC z (formulaHead (formulaTail g.skel.formula)) := by
  unfold renderNode
  rcases h with h | h | h | h | h | h <;> (rw [h]; rfl)
theorem rn_dec_tt (h : g.skel.state = .s2 ∨ g.skel.state = .s5 ∨ g.skel.state = .s6 ∨ g.skel.state = .s7 ∨
    g.skel.state = .s8 ∨ g.skel.state = .s9) :
    (renderNode z α g).row.2.2.2.f_tt = encC z (formulaTail (formulaTail g.skel.formula)) := by
  unfold renderNode
  rcases h with h | h | h | h | h | h <;> (rw [h]; rfl)
theorem rn_dec_tth (h : g.skel.state = .s6) :
    (renderNode z α g).row.2.2.2.f_tth = encC z (formulaHead (formulaTail (formulaTail g.skel.formula))) := by
  unfold renderNode; rw [h]; rfl
theorem rn_dec_ttt (h : g.skel.state = .s6) :
    (renderNode z α g).row.2.2.2.f_ttt = encC z (formulaTail (formulaTail (formulaTail g.skel.formula))) := by
  unfold renderNode; rw [h]; rfl

end Render

theorem imOK : ∀ r : Fin 63, r.val / 3 ∈ [0, 1, 2, 5, 7, 12, 13, 14, 15, 16, 17] → fullImMap.ext r ≠ none := by
  decide +kernel

section RowRoles
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [DecidableEq F] {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))] {hC : ℕ} {S : MemShape}
variable (V : VerifierData F K hC S) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ)) {fuel : ℕ}
  {subject formula : Noun} {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))} {result : Noun}
  (hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel subject formula = .ok (t, result))
  (accX accP : ℕ → Quad (algebraMap F K δ))
  (hnodes : ∀ i : Fin V.N, V.computeNodes i = V.orbitC.ω ^ (i : ℕ)) (hsize : V.N ≤ 2 ^ hC)

include hnodes hsize in
/-- A role entry of the honest row `j` reads the row's role value. -/
theorem env_entry_role (j : ℕ) (hj : j < V.N) (r : Fin 63) (hne : fullImMap.ext r ≠ none) :
    Q.val δ (entryQ F (.k (13 + 3 * (r : ℕ)))) (gatherEnv V.basis (envAcc V χ αs hgen accX accP j))
        (envAcc V χ αs hgen accX accP j) = (rowsAcc V χ αs hgen accX accP ⟨j, hj⟩).ext r := by
  rw [envAcc_eq V χ αs hgen accX accP j hj]
  exact entryQ_role_val V.basis V.computeNodes (injective_of_pow V hnodes hsize) _ _ _ _ _ r hne

include hnodes hsize in
theorem roleFP_pub (j : ℕ) (hj : j < V.N) (hjn : j < nRows t) (k : Fin 12)
    (hkl : (k : ℕ) = 0 ∨ (k : ℕ) = 1 ∨ (k : ℕ) = 2 ∨ (k : ℕ) = 5 ∨ (k : ℕ) = 7)
    (hk : k = 1 ∨ ((gRow t j).skel.state = .s0 ∧ (k = 0 ∨ k = 2)) ∨
      ((gRow t j).skel.state = .s9 ∧ (k = 5 ∨ k = 7))) :
    RoleFP δ V.basis (envAcc V χ αs hgen accX accP j) (3 * (k : ℕ))
      (pubFingerprint (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.1 k) := by
  intro c
  have hc := c.isLt
  have hr : 3 * (k : ℕ) + c < 58 := by omega
  have hq := env_entry_role V χ αs hgen accX accP hnodes hsize j hj ⟨3 * (k : ℕ) + c, by omega⟩
    (imOK _ (by
      show (3 * (k : ℕ) + c) / 3 ∈ _
      rw [show (3 * (k : ℕ) + c) / 3 = k by omega]
      rcases hkl with h | h | h | h | h <;> rw [h] <;> simp))
  have e1 := rowsAcc_ext_lt V χ αs hgen accX accP ⟨j, hj⟩ (3 * (k : ℕ) + c) hr
  have e2 := genWalk_bfsPubAt (zQuad δ χ) αs (ιc χ ⟨8, by decide⟩) (ιc χ ⟨9, by decide⟩) (ιc χ ⟨10, by decide⟩) t j hjn
  have e3 := role_pub (F := F) (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.1
    (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.2
    (honestEx ⟨αs, zQuad δ χ, ιc χ ⟨8, by decide⟩, ιc χ ⟨9, by decide⟩, ιc χ ⟨10, by decide⟩⟩
      (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.1 (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.2)
    (honestOverlay (fun k => childStateTagCol (Walk.bfsForest [genWalkRoot (zQuad δ χ) αs (ιc χ ⟨8, by decide⟩) (ιc χ ⟨9, by decide⟩) (ιc χ ⟨10, by decide⟩) t]) (j + 1) k)
      (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.1) k c
    (by rw [renderNode_state_eq]; exact hk) hr
  show Q.val δ (entryQ F (.k (13 + 3 * (3 * (k : ℕ) + c)))) _ _ = _
  rw [hq, e1]
  simp only [coreAt]
  rw [e2]
  exact e3

include hnodes hsize in
theorem roleFP_dec (j : ℕ) (hj : j < V.N) (hjn : j < nRows t) (k : Fin 6) :
    RoleFP δ V.basis (envAcc V χ αs hgen accX accP j) (36 + 3 * (k : ℕ))
      (decFingerprint (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.2 k) := by
  intro c
  have hc := c.isLt
  have hk := k.isLt
  have hr : 36 + 3 * (k : ℕ) + c < 58 := by omega
  have hq := env_entry_role V χ αs hgen accX accP hnodes hsize j hj ⟨36 + 3 * (k : ℕ) + c, by omega⟩
    (imOK _ (by
      show (36 + 3 * (k : ℕ) + c) / 3 ∈ _
      rw [show (36 + 3 * (k : ℕ) + c) / 3 = 12 + k by omega]
      have : (k : ℕ) = 0 ∨ (k : ℕ) = 1 ∨ (k : ℕ) = 2 ∨ (k : ℕ) = 3 ∨ (k : ℕ) = 4 ∨ (k : ℕ) = 5 := by omega
      rcases this with h | h | h | h | h | h <;> rw [h] <;> simp))
  have e1 := rowsAcc_ext_lt V χ αs hgen accX accP ⟨j, hj⟩ (36 + 3 * (k : ℕ) + c) hr
  have e2 := genWalk_bfsPubAt (zQuad δ χ) αs (ιc χ ⟨8, by decide⟩) (ιc χ ⟨9, by decide⟩) (ιc χ ⟨10, by decide⟩) t j hjn
  have e3 := role_dec (F := F) (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.1
    (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.2
    (honestEx ⟨αs, zQuad δ χ, ιc χ ⟨8, by decide⟩, ιc χ ⟨9, by decide⟩, ιc χ ⟨10, by decide⟩⟩
      (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.1 (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.2)
    (honestOverlay (fun k => childStateTagCol (Walk.bfsForest [genWalkRoot (zQuad δ χ) αs (ιc χ ⟨8, by decide⟩) (ιc χ ⟨9, by decide⟩) (ιc χ ⟨10, by decide⟩) t]) (j + 1) k)
      (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.1) k c hr
  show Q.val δ (entryQ F (.k (13 + 3 * (36 + 3 * (k : ℕ) + c)))) _ _ = _
  rw [hq, e1]
  simp only [coreAt]
  rw [e2]
  exact e3

end RowRoles

theorem recQ0_lt {F : Type} [Field F] (c : Fin 11) (h : (c : ℕ) < 10) :
    recQ0 F c = entryQ F (formulaRec ⟨c, h⟩) := by
  simp [recQ0, h]

theorem recQ0_last {F : Type} [Field F] : recQ0 F 10 = qconst F 1 := by
  simp [recQ0]

theorem hdN_of_cell {n : Noun} (h : n.isCell = true) : hdN n = formulaHead n := by
  cases n with
  | atom _ => simp [Noun.isCell] at h
  | cell _ _ => rfl

theorem tlN_of_cell {n : Noun} (h : n.isCell = true) : tlN n = formulaTail n := by
  cases n with
  | atom _ => simp [Noun.isCell] at h
  | cell _ _ => rfl

section RecVec
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))] {b : Basis (Fin 3) F K} {E : Env F}

/-- **Slot `0`'s record vector is the export request `xReq` of the formula cell at side `1`.** -/
theorem rec0_vec (z : Quad (algebraMap F K δ)) (cells : List Noun) (f : Noun)
    (hA : RoleFP δ b E roleF (GlobalCarryRecognizer.enc z f))
    (hB : RoleFP δ b E roleFh (GlobalCarryRecognizer.enc z (hdN f)))
    (hC : RoleFP δ b E roleFt (GlobalCarryRecognizer.enc z (tlN f)))
    (hi : Q.val δ (entryQ F (.f fIdxCol)) (gatherEnv b E) E = liftQ δ (cells.idxOf f : F)) :
    (fun c : Fin 11 => Q.val δ (recQ0 F c) (gatherEnv b E) E) = xReq δ z cells f true := by
  have hv := recValQ_exportRec hA hB hC hi
  funext c
  fin_cases c
  · exact congrFun hv 0
  · exact congrFun hv 1
  · exact congrFun hv 2
  · exact congrFun hv 3
  · exact congrFun hv 4
  · exact congrFun hv 5
  · exact congrFun hv 6
  · exact congrFun hv 7
  · exact congrFun hv 8
  · exact congrFun hv 9
  · show Q.val δ (recQ0 F 10) _ _ = _
    rw [recQ0_last, qconst_val]
    simp [xReq, liftQ]

/-- **An export record at side `0` (width `10`) compresses as the width-`11` request `xReq` at side `0`.** -/
theorem export10_compress (γ ρ z : Quad (algebraMap F K δ)) (cells : List Noun) (n : Noun) {p l r idx : ℕ}
    (hA : RoleFP δ b E p (GlobalCarryRecognizer.enc z n))
    (hB : RoleFP δ b E l (GlobalCarryRecognizer.enc z (hdN n)))
    (hC : RoleFP δ b E r (GlobalCarryRecognizer.enc z (tlN n)))
    (hi : Q.val δ (entryQ F (.f idx)) (gatherEnv b E) E = liftQ δ (cells.idxOf n : F)) :
    FiniteIO.compress (m := 10) ⟨γ, ρ⟩ (recValQ δ (gatherEnv b E) E (exportRec p l r idx)) =
      FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xReq δ z cells n false) := by
  rw [compress11_of_last_zero γ ρ _ (by simp [xReq])]
  congr 1
  rw [recValQ_exportRec hA hB hC hi]
  funext i
  fin_cases i <;> rfl

/-- **A path record equals the path-provide request `pReq`** of the read `(root, ax)`. -/
theorem path_vec (z : Quad (algebraMap F K δ)) (cells : List Noun) (root child : Noun) (ax : ℕ)
    (hchild : (Noun.slot ax root).getD (.atom 0) = child) {rr cc axc idx : ℕ}
    (hA : RoleFP δ b E rr (GlobalCarryRecognizer.enc z root))
    (hB : RoleFP δ b E cc (GlobalCarryRecognizer.enc z child))
    (ha : Q.val δ (entryQ F (.f axc)) (gatherEnv b E) E = liftQ δ (ax : F))
    (hi : Q.val δ (entryQ F (.f idx)) (gatherEnv b E) E = liftQ δ (cells.idxOf root : F)) :
    recValQ δ (gatherEnv b E) E (pathRec rr cc axc idx) = pReq δ z cells (root, ax) := by
  rw [recValQ_pathRec hA hB ha hi]
  simp only [pReq, hchild]

end RecVec

section RowRecs
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [DecidableEq F] {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))] {hC : ℕ} {S : MemShape}
variable (V : VerifierData F K hC S) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ)) {fuel : ℕ}
  {subject formula : Noun} {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))} {result : Noun}
  (hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel subject formula = .ok (t, result))
  (accX accP : ℕ → Quad (algebraMap F K δ))
  (hnodes : ∀ i : Fin V.N, V.computeNodes i = V.orbitC.ω ^ (i : ℕ)) (hsize : V.N ≤ 2 ^ hC)

include hnodes hsize in
theorem col_fIdx (j : ℕ) (hj : j < V.N) :
    Q.val δ (entryQ F (.f fIdxCol)) (gatherEnv V.basis (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j))
      (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j) =
      liftQ δ (((demT t).cells.idxOf (gRow t j).skel.formula : ℕ) : F) := by
  rw [envAcc_entry_f V χ αs hgen _ _ hnodes hsize j hj fIdxCol (by unfold fIdxCol; omega)]
  congr 1

include hnodes hsize in
theorem col_vI (j : ℕ) (hj : j < V.N) (k : Fin 2) :
    Q.val δ (entryQ F (.f (vIdxCol k))) (gatherEnv V.basis (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j))
      (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j) =
      liftQ δ (((demT t).cells.idxOf ((((rowSlotKeys (gRow t j))[(k : ℕ) + 1]?).map Prod.fst).getD (.atom 0)) : ℕ) : F) := by
  rw [envAcc_entry_f V χ αs hgen _ _ hnodes hsize j hj (vIdxCol k) (by unfold vIdxCol; have := k.isLt; omega)]
  congr 1
  rw [rowsAcc_vcl]
  fin_cases k
  · simp [vclFill, vIdxCol, vIT]
  · simp [vclFill, vIdxCol, vIT]

include hnodes hsize in
theorem col_ax (j : ℕ) (hj : j < V.N) :
    Q.val δ (entryQ F (.f axCol)) (gatherEnv V.basis (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j))
      (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j) =
      liftQ δ ((honestAx (gRow t j).skel : ℕ) : F) := by
  rw [envAcc_entry_f V χ αs hgen _ _ hnodes hsize j hj axCol (by unfold axCol; omega)]
  congr 1

theorem row_coins (j : ℕ) (hj : j < V.N) :
    coinsQ δ (gatherEnv V.basis (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j))
      (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j) = ⟨γC (δF := δ) χ, ρC (δF := δ) χ⟩ := by
  rw [coinsQ_chalVQ7T δ V.basis χ _ (envAcc_chal V χ αs hgen _ _ j hj)]
  rfl

include hnodes hsize in
/-- **The honest slot inverses are the reciprocals of the denominators at the row environment** (accumulators
zeroed or not: the denominators read no accumulator). -/
theorem row_inv (j : ℕ) (hj : j < V.N) :
    Q.val δ (invQ F inv0Base (invImBase 0)) (gatherEnv V.basis (envAcc V χ αs hgen accX accP j))
        (envAcc V χ αs hgen accX accP j) =
      (den0Q δ (gatherEnv V.basis (envAcc V χ αs hgen accX accP j)) (envAcc V χ αs hgen accX accP j))⁻¹ ∧
    Q.val δ (invQ F (lookupInvBase 0) (invImBase 1)) (gatherEnv V.basis (envAcc V χ αs hgen accX accP j))
        (envAcc V χ αs hgen accX accP j) =
      (den1Q δ (gatherEnv V.basis (envAcc V χ αs hgen accX accP j)) (envAcc V χ αs hgen accX accP j))⁻¹ ∧
    Q.val δ (invQ F (lookupInvBase 1) (invImBase 2)) (gatherEnv V.basis (envAcc V χ αs hgen accX accP j))
        (envAcc V χ αs hgen accX accP j) =
      (den2Q δ (gatherEnv V.basis (envAcc V χ αs hgen accX accP j)) (envAcc V χ αs hgen accX accP j))⁻¹ := by
  have hinj := injective_of_pow V hnodes hsize
  rw [envAcc_eq V χ αs hgen accX accP j hj]
  obtain ⟨e0, e1, e2⟩ := inv_final_eq V.basis χ αs (walkT χ αs hgen) V.N (decT χ αs t) serT (axT t) (fIdxT t)
    (vIT t 1) (vIT t 2) accX accP V.computeNodes hinj V.orbitC.ω (chalVQ7T δ V.basis χ)
    (pubCFT δ V (xT t) (reqT t χ) χ) ⟨j, hj⟩
  have hq := vclFill_invQ V.basis V.computeNodes hinj (rowsAcc V χ αs hgen accX accP) V.orbitC.ω
    (chalVQ7T δ V.basis χ) (pubCFT δ V (xT t) (reqT t χ) χ) ⟨j, hj⟩ (serT j) (axT t j)
    (fIdxT t j) (vIT t 1 j) (vIT t 2 j) _ _ _ (accX j) (accP j)
    (funext fun c => rowsAcc_vcl V χ αs hgen accX accP ⟨j, hj⟩ c)
  exact ⟨hq.1.trans e0, hq.2.1.trans e1, hq.2.2.trans e2⟩

theorem rowsAcc_base (i : Fin V.N) (hi : (i : ℕ) < nRows t) :
    (rowsAcc V χ αs hgen accX accP i).base = fun c : Fin 13 =>
      if (c : ℕ) < 11 then (if (c : ℕ) = stT t i then (1 : F) else 0)
      else if (c : ℕ) = 11 then (if (i : ℕ) = 0 then (1 : F) else 0)
      else (if (i : ℕ) + 1 = V.N then (1 : F) else 0) := by
  have := walkT_state χ αs hgen i hi
  show (genRowVals _ _ _ _ _ _ _ _ _ _ _ _ _).base = _
  funext c
  simp only [genRowVals, honestWalkOf_pubAt, this, stT]
  rfl

include hnodes hsize in
theorem row_sel (j : ℕ) (hj : j < V.N) (hjn : j < nRows t) :
    ∀ c, c < 11 → (envAcc V χ αs hgen accX accP j).trace c = if c = stT t j then 1 else 0 := by
  intro c hc
  rw [envAcc_eq V χ αs hgen accX accP j hj,
    env_honestQT_trace V.basis V.computeNodes (injective_of_pow V hnodes hsize) _ _ _ _ _
      (by simp only [vclWidthT]; omega)]
  simp only [vclColT, show c < 202 by omega, if_true, srcColT, show c < 13 by omega, dif_pos]
  rw [rowsAcc_base V χ αs hgen accX accP ⟨j, hj⟩ hjn]
  simp [hc]

end RowRecs

def PS (s : State) : Prop := s = .s2 ∨ s = .s5 ∨ s = .s6 ∨ s = .s7 ∨ s = .s8 ∨ s = .s9
instance (s : State) : Decidable (PS s) := by unfold PS; infer_instance

theorem exp_slots : ∀ s : State, ((List.finRange 3).filter fun j => slotAcc s j = some .export) =
    (0 : Fin 3) :: ((if PS s then [(1 : Fin 3)] else []) ++ (if s = .s6 then [(2 : Fin 3)] else [])) := by
  decide

theorem path_slots : ∀ s : State, ((List.finRange 3).filter fun j => slotAcc s j = some .path) =
    (if s = .s0 then [(1 : Fin 3)] else []) ++ (if s = .s9 then [(2 : Fin 3)] else []) := by
  decide

theorem rowExportKeys_eq {L : Type} [Field L] (g : GenComputeRow L) (k0 k1 k2 : Noun × ℕ)
    (h0 : (rowSlotKeys g)[0]? = some k0)
    (h1 : PS g.skel.state → (rowSlotKeys g)[1]? = some k1)
    (h2 : g.skel.state = .s6 → (rowSlotKeys g)[2]? = some k2) :
    rowExportKeys g = k0 :: ((if PS g.skel.state then [k1] else []) ++ (if g.skel.state = .s6 then [k2] else [])) := by
  unfold rowExportKeys rowKeysAt
  rw [exp_slots]
  have h6 : g.skel.state = .s6 → PS g.skel.state := fun h => by rw [h]; decide
  by_cases hP : PS g.skel.state <;> by_cases h6' : g.skel.state = .s6
  · simp only [if_pos hP, if_pos h6']; simp [h0, h1 hP, h2 h6']
  · simp only [if_pos hP, if_neg h6']; simp [h0, h1 hP]
  · exact absurd (h6 h6') hP
  · simp only [if_neg hP, if_neg h6']; simp [h0]

theorem rowPathKeys_eq {L : Type} [Field L] (g : GenComputeRow L) (k1 k2 : Noun × ℕ)
    (h1 : g.skel.state = .s0 → (rowSlotKeys g)[1]? = some k1)
    (h2 : g.skel.state = .s9 → (rowSlotKeys g)[2]? = some k2) :
    rowPathKeys g = (if g.skel.state = .s0 then [k1] else []) ++ (if g.skel.state = .s9 then [k2] else []) := by
  unfold rowPathKeys rowKeysAt
  rw [path_slots]
  by_cases a0 : g.skel.state = .s0 <;> by_cases a9 : g.skel.state = .s9
  · rw [a0] at a9; cases a9
  · simp only [if_pos a0, if_neg a9]; simp [h1 a0]
  · simp only [if_neg a0, if_pos a9]; simp [h2 a9]
  · simp only [if_neg a0, if_neg a9]; simp

theorem shallowSided_append (l1 l2 : List (Noun × ℕ)) :
    shallowSided (l1 ++ l2) = shallowSided l1 ++ shallowSided l2 := by
  simp [shallowSided, shallowReads, List.filter_append, List.flatMap_append]

theorem shallowSided_single (n : Noun) (a : ℕ) (hd : depthOf a = 1) (hc : n.isCell = true) :
    shallowSided [(n, a)] = [(n, decide (a % 2 = 1))] := by
  cases n with
  | atom _ => simp [Noun.isCell] at hc
  | cell x y => simp [shallowSided, shallowReads, hd, selfCell]

theorem depthOf_two : depthOf 2 = 1 := by decide

/-- **The export side of a row**: its `shallowSided` request sum is `Φ f 1 + [PS] Φ tl 0 + [s6] Φ tt 0`. -/
theorem rhsX_eq {L : Type} [Field L] {M : Type} [AddCommMonoid M] (g : GenComputeRow L) (f tl tt : Noun)
    (Φ : Noun → Bool → M)
    (h0 : (rowSlotKeys g)[0]? = some (f, 3)) (hf : f.isCell = true)
    (h1 : PS g.skel.state → (rowSlotKeys g)[1]? = some (tl, 2) ∧ tl.isCell = true)
    (h2 : g.skel.state = .s6 → (rowSlotKeys g)[2]? = some (tt, 2) ∧ tt.isCell = true) :
    ((shallowSided (rowExportKeys g)).map fun c => Φ c.1 c.2).sum =
      Φ f true + ((if PS g.skel.state then Φ tl false else 0) + (if g.skel.state = .s6 then Φ tt false else 0)) := by
  rw [rowExportKeys_eq g (f, 3) (tl, 2) (tt, 2) h0 (fun h => (h1 h).1) (fun h => (h2 h).1)]
  have s3 : shallowSided [(f, 3)] = [(f, true)] := by
    rw [shallowSided_single f 3 depthOf_three hf]; rfl
  have e1 : ∀ hP : PS g.skel.state, shallowSided [(tl, 2)] = [(tl, false)] := fun hP => by
    rw [shallowSided_single tl 2 depthOf_two (h1 hP).2]; rfl
  have e2 : ∀ h6 : g.skel.state = .s6, shallowSided [(tt, 2)] = [(tt, false)] := fun h6 => by
    rw [shallowSided_single tt 2 depthOf_two (h2 h6).2]; rfl
  have hs : shallowSided (((f, 3) : Noun × ℕ) :: ((if PS g.skel.state then [(tl, 2)] else []) ++
      (if g.skel.state = .s6 then [(tt, 2)] else []))) =
      [(f, true)] ++ ((if PS g.skel.state then [(tl, false)] else []) ++
        (if g.skel.state = .s6 then [(tt, false)] else [])) := by
    rw [show (((f, 3) : Noun × ℕ) :: ((if PS g.skel.state then [(tl, 2)] else []) ++
      (if g.skel.state = .s6 then [(tt, 2)] else []))) = [(f, 3)] ++ ((if PS g.skel.state then [(tl, 2)] else []) ++
      (if g.skel.state = .s6 then [(tt, 2)] else [])) from rfl, shallowSided_append, shallowSided_append, s3]
    congr 2
    · by_cases hP : PS g.skel.state
      · simp only [if_pos hP]; exact e1 hP
      · simp only [if_neg hP]; rfl
    · by_cases h6 : g.skel.state = .s6
      · simp only [if_pos h6]; exact e2 h6
      · simp only [if_neg h6]; rfl
  rw [hs]
  by_cases hP : PS g.skel.state <;> by_cases h6 : g.skel.state = .s6
  · simp only [if_pos hP, if_pos h6]; simp
  · simp only [if_pos hP, if_neg h6]; simp
  · simp only [if_neg hP, if_pos h6]; simp
  · simp only [if_neg hP, if_neg h6]; simp

/-- **The path side of a row**: the filtered path keys' sum is `[s0] Ψ r₁ + [s9] Ψ r₂`. -/
theorem rhsP_eq {L : Type} [Field L] {M : Type} [AddCommMonoid M] (g : GenComputeRow L) (r1 r2 : Noun × ℕ)
    (Ψ : Noun × ℕ → M)
    (h1 : g.skel.state = .s0 → (rowSlotKeys g)[1]? = some r1 ∧ isPathAx r1.2 = true)
    (h2 : g.skel.state = .s9 → (rowSlotKeys g)[2]? = some r2 ∧ isPathAx r2.2 = true) :
    (((rowPathKeys g).filter fun r => isPathAx r.2).map Ψ).sum =
      (if g.skel.state = .s0 then Ψ r1 else 0) + (if g.skel.state = .s9 then Ψ r2 else 0) := by
  rw [rowPathKeys_eq g r1 r2 (fun h => (h1 h).1) (fun h => (h2 h).1)]
  by_cases a0 : g.skel.state = .s0 <;> by_cases a9 : g.skel.state = .s9
  · rw [a0] at a9; cases a9
  · simp only [if_pos a0, if_neg a9]; simp [(h1 a0).2]
  · simp only [if_neg a0, if_pos a9]; simp [(h2 a9).2]
  · simp only [if_neg a0, if_neg a9]; simp

section DenVal
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (eK : Env K) (E : Env F)

theorem den1Q_val (s : ℕ) (hsel : ∀ j, j < 11 → E.trace j = if j = s then 1 else 0) :
    den1Q δ eK E =
      (if s = 0 then FiniteIO.compress (coinsQ δ eK E) (recValQ δ eK E op0PathRec) else 0) +
      (if s ∈ slot1ExportSels then FiniteIO.compress (coinsQ δ eK E) (recValQ δ eK E tailRec) else 0) := by
  unfold den1Q
  rw [qlift_selVar_oh δ eK E s hsel 0 (by norm_num),
    qlift_selSum_oh δ eK E s hsel slot1ExportSels (by decide) (by decide)]
  have e0 : (0 = s) = (s = 0) := propext eq_comm
  simp only [e0]
  by_cases a : s = 0 <;> by_cases b : s ∈ slot1ExportSels <;> simp [a, b]

theorem den2Q_val (s : ℕ) (hsel : ∀ j, j < 11 → E.trace j = if j = s then 1 else 0) :
    den2Q δ eK E =
      (if s = 6 then FiniteIO.compress (coinsQ δ eK E) (recValQ δ eK E ttRec) else 0) +
      (if s = 9 then FiniteIO.compress (coinsQ δ eK E) (recValQ δ eK E op9PathRec) else 0) := by
  unfold den2Q
  rw [qlift_selVar_oh δ eK E s hsel 6 (by norm_num), qlift_selVar_oh δ eK E s hsel 9 (by norm_num)]
  have e6 : (6 = s) = (s = 6) := propext eq_comm
  have e9 : (9 = s) = (s = 9) := propext eq_comm
  simp only [e6, e9]
  by_cases a : s = 6 <;> by_cases b : s = 9 <;> simp [a, b]

end DenVal

theorem stT_facts (st : State) :
    ((stateIndex st : ℕ) ∈ slot1ExportSels ↔ PS st) ∧ ((stateIndex st : ℕ) = 6 ↔ st = .s6) ∧
    ((stateIndex st : ℕ) = 0 ↔ st = .s0) ∧ ((stateIndex st : ℕ) = 9 ↔ st = .s9) := by
  cases st <;> decide

section GRowFacts
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] {δ : F}
  [Fact (¬ IsSquare (algebraMap F K δ))]

theorem RowShape_congr {L : Type} [Field L] {g1 g2 : GenComputeRow L} (hs : g1.skel = g2.skel)
    (hr : g1.requests = g2.requests) : RowShape g1 → RowShape g2 := by
  have : rowSlotKeys g1 = rowSlotKeys g2 := by simp [rowSlotKeys, hr]
  unfold RowShape
  rw [hs, this]
  exact id

/-- **The request shapes and slot `0` at every walk row `j < nRows t`** (the row `gRow t j` carries the label
of a node of `t`: `gRow t j`'s skeleton and requests are those of a BFS row of the AIR-reordered tree). -/
theorem gRow_facts {fuel : ℕ} {S Fm : Noun} {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))} {r : Noun}
    (h : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel S Fm = .ok (t, r)) (j : ℕ) (hj : j < nRows t) :
    RowShape (gRow t j) ∧ (gRow t j).skel.formula.isCell = true ∧
      (rowSlotKeys (gRow t j)).head? = some ((gRow t j).skel.formula, 3) := by
  have hi : j + 1 - 1 < (bfsRows (airReorder t)).length := by
    rw [bfsRows_length]; simp only [nRows] at hj; omega
  have hreq := bfsLabelAt_requests (airReorder t) (j + 1) hi
  have hskel := bfsLabelAt_skel (airReorder t) (j + 1) hi
  have hmem : (bfsRows (airReorder t))[j + 1 - 1] ∈ (bfsForest [airReorder t]).map NTree.label :=
    List.getElem_mem hi
  obtain ⟨u, hu, hul⟩ := List.mem_map.mp hmem
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ u).mp hu
  simp only [List.mem_singleton] at hc
  subst hc
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label t u hin
  have hsh := gen_rowShape fuel S Fm t r h u0 hu0
  have h0 := genComputeSkeleton_slot0 fuel S Fm t r h u0 hu0
  have e1 : (gRow t j).skel = u0.label.skel := by
    show (bfsLabelAt (airReorder t) (j + 1)).skel = _
    rw [hskel, ← hul, hl]
  have e2 : (gRow t j).requests = u0.label.requests := by
    show (bfsLabelAt (airReorder t) (j + 1)).requests = _
    rw [hreq, ← hul, hl]
  have e3 : rowSlotKeys (gRow t j) = rowSlotKeys u0.label := by simp [rowSlotKeys, e2]
  refine ⟨RowShape_congr e1.symm e2.symm hsh, ?_, ?_⟩
  · rw [e1]; exact h0.1
  · rw [e3, e1]; exact h0.2

end GRowFacts

section TermVal
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K) (E : Env F)

theorem invQ_val (re im : ℕ) :
    Q.val δ (invQ F re im) (gatherEnv b E) E =
      Quad.mk _ (LogUp.limbVal b E.trace re) (LogUp.limbVal b E.trace im) := by
  simp [invQ, qcol, Q.val, MixedExpr.eval, gatherEnv]

theorem slot1ExportSels_val : slot1ExportSels = [2, 5, 6, 7, 8, 9] := by decide

theorem termQ_X_val (s : ℕ) (hsel : ∀ j, j < 11 → E.trace j = if j = s then 1 else 0) :
    termQ δ b accSlotsX accSlotsXIm E =
      Q.val δ (invQ F inv0Base (invImBase 0)) (gatherEnv b E) E +
      (if s ∈ slot1ExportSels then Q.val δ (invQ F (lookupInvBase 0) (invImBase 1)) (gatherEnv b E) E else 0) +
      (if s = 6 then Q.val δ (invQ F (lookupInvBase 1) (invImBase 2)) (gatherEnv b E) E else 0) := by
  have h1 := selSum_eval_oh E s hsel slot1ExportSels (by decide) (by decide)
  have h6 := selVar_eval_oh E s hsel 6 (by norm_num)
  simp only [termQ, termVal, accSlotsX, accSlotsXIm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, h1, h6, CoeffExpr.eval, invQ_val]
  have e6 : (6 = s) = (s = 6) := propext eq_comm
  simp only [e6]
  by_cases a1 : s ∈ slot1ExportSels <;> by_cases a6 : s = 6
  · simp only [eq_true a1, eq_true a6, if_true]; simp [Quad.mk_add, add_assoc]
  · simp only [eq_true a1, eq_false a6, if_true, if_false]; simp [Quad.mk_add]
  · simp only [eq_false a1, eq_true a6, if_true, if_false]; simp [Quad.mk_add]
  · simp only [eq_false a1, eq_false a6, if_true, if_false]; simp [Quad.mk_add]

theorem termQ_P_val (s : ℕ) (hsel : ∀ j, j < 11 → E.trace j = if j = s then 1 else 0) :
    termQ δ b accSlotsP accSlotsPIm E =
      (if s = 0 then Q.val δ (invQ F (lookupInvBase 0) (invImBase 1)) (gatherEnv b E) E else 0) +
      (if s = 9 then Q.val δ (invQ F (lookupInvBase 1) (invImBase 2)) (gatherEnv b E) E else 0) := by
  have h0 := selVar_eval_oh E s hsel 0 (by norm_num)
  have h9 := selVar_eval_oh E s hsel 9 (by norm_num)
  simp only [termQ, termVal, accSlotsP, accSlotsPIm, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, h0, h9, CoeffExpr.eval, invQ_val]
  have e0 : (0 = s) = (s = 0) := propext eq_comm
  have e9 : (9 = s) = (s = 9) := propext eq_comm
  simp only [e0, e9]
  by_cases a0 : s = 0 <;> by_cases a9 : s = 9
  · omega
  · simp only [eq_true a0, eq_false a9, if_true, if_false]; simp [Quad.mk_add]
  · simp only [eq_false a0, eq_true a9, if_true, if_false]; simp [Quad.mk_add]
  · simp only [eq_false a0, eq_false a9, if_true, if_false]; simp [Quad.mk_zero']

/-- At a `z1 = 0` row the tower-local path term is the shared one. -/
theorem termQ_PT_of_z0 (hz : E.trace z1Col = 0) :
    termQ δ b accSlotsPT accSlotsPImT E = termQ δ b accSlotsP accSlotsPIm E := by
  unfold termQ
  congr 1 <;>
    simp [termVal, accSlotsPT, accSlotsP, accSlotsPImT, accSlotsPIm, actP0, actP9, notZ1, selVar,
      CoeffExpr.eval, hz]

/-- At a `z1 = 1` row the path term is `0` (no path request). -/
theorem termQ_PT_of_z1 (hz : E.trace z1Col = 1) :
    termQ δ b accSlotsPT accSlotsPImT E = 0 := by
  unfold termQ
  have h1 : termVal b accSlotsPT E = 0 := by
    simp [termVal, accSlotsPT, actP0, actP9, notZ1, selVar, CoeffExpr.eval, hz]
  have h2 : termVal b accSlotsPImT E = 0 := by
    simp [termVal, accSlotsPImT, actP0, actP9, notZ1, selVar, CoeffExpr.eval, hz]
  rw [h1, h2]; exact Quad.mk_zero' (algebraMap F K δ)

end TermVal

theorem dec_ft_eq {L : Type} [Field L] (z α : L) (g : GenComputeRow L) (hsh : RowShape g) :
    (renderNode z α g).row.2.2.2.f_t = encC z (formulaTail g.skel.formula) := by
  by_cases hs : g.skel.state = .s1
  · rw [rn_dec_t_s1 z α g hs, hsh.1 hs]
  · exact rn_dec_t_ne z α g hs

section RowFinal
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [DecidableEq F] {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))] {hC : ℕ} {S : MemShape}
variable (V : VerifierData F K hC S) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ)) {fuel : ℕ}
  {subject formula : Noun} {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))} {result : Noun}
  (hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel subject formula = .ok (t, result))
  (hnodes : ∀ i : Fin V.N, V.computeNodes i = V.orbitC.ω ^ (i : ℕ)) (hsize : V.N ≤ 2 ^ hC)
  (j : ℕ) (hj : j < V.N) (hjn : j < nRows t)
  (hsh : RowShape (gRow t j)) (hcell : (gRow t j).skel.formula.isCell = true)

include hnodes hsize hj hjn hsh hcell in
theorem row_den0 :
    den0Q δ (gatherEnv V.basis (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j))
        (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j) =
      FiniteIO.compress (m := 11) ⟨γC (δF := δ) χ, ρC (δF := δ) χ⟩
        (xReq δ (zQuad δ χ) (demT t).cells (gRow t j).skel.formula true) := by
  show FiniteIO.compress (coinsQ δ _ _) (fun c => Q.val δ (recQ0 F c) _ _) = _
  rw [row_coins V χ αs hgen j hj]
  congr 1
  have hA := roleFP_pub V χ αs hgen (fun _ => 0) (fun _ => 0) hnodes hsize j hj hjn 1 (by simp) (Or.inl rfl)
  have hB := roleFP_dec V χ αs hgen (fun _ => 0) (fun _ => 0) hnodes hsize j hj hjn 0
  have hC' := roleFP_dec V χ αs hgen (fun _ => 0) (fun _ => 0) hnodes hsize j hj hjn 1
  rw [show pubFingerprint (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.1 1 =
    GlobalCarryRecognizer.enc (zQuad δ χ) (gRow t j).skel.formula from
      (rn_pub_f _ _ _).trans (encC_eq _ _)] at hA
  rw [show decFingerprint (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.2 0 =
    GlobalCarryRecognizer.enc (zQuad δ χ) (hdN (gRow t j).skel.formula) from
      (((rn_dec_h _ _ _).trans (by rw [hdN_of_cell hcell])).trans (encC_eq _ _))] at hB
  rw [show decFingerprint (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.2 1 =
    GlobalCarryRecognizer.enc (zQuad δ χ) (tlN (gRow t j).skel.formula) from
      ((dec_ft_eq _ _ _ hsh).trans (by rw [tlN_of_cell hcell])).trans (encC_eq _ _)] at hC'
  exact rec0_vec (zQuad δ χ) (demT t).cells _ hA hB hC' (col_fIdx V χ αs hgen hnodes hsize j hj)

include hnodes hsize hj hjn hsh hcell in
theorem row_rec1 (hPS : PS (gRow t j).skel.state) :
    FiniteIO.compress (coinsQ δ (gatherEnv V.basis (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j))
        (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j))
      (recValQ δ (gatherEnv V.basis (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j))
        (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j) tailRec) =
      FiniteIO.compress (m := 11) ⟨γC (δF := δ) χ, ρC (δF := δ) χ⟩
        (xReq δ (zQuad δ χ) (demT t).cells (formulaTail (gRow t j).skel.formula) false) := by
  rw [row_coins V χ αs hgen j hj]
  obtain ⟨hk, htc⟩ := hsh.2.1 (by rcases hPS with h | h | h | h | h | h <;> simp [h])
  have hA := roleFP_dec V χ αs hgen (fun _ => 0) (fun _ => 0) hnodes hsize j hj hjn 1
  have hB := roleFP_dec V χ αs hgen (fun _ => 0) (fun _ => 0) hnodes hsize j hj hjn 2
  have hC' := roleFP_dec V χ αs hgen (fun _ => 0) (fun _ => 0) hnodes hsize j hj hjn 3
  have hps : (gRow t j).skel.state = .s2 ∨ (gRow t j).skel.state = .s5 ∨ (gRow t j).skel.state = .s6 ∨
      (gRow t j).skel.state = .s7 ∨ (gRow t j).skel.state = .s8 ∨ (gRow t j).skel.state = .s9 := hPS
  rw [show decFingerprint (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.2 1 =
    GlobalCarryRecognizer.enc (zQuad δ χ) (formulaTail (gRow t j).skel.formula) from
      (dec_ft_eq _ _ _ hsh).trans (encC_eq _ _)] at hA
  rw [show decFingerprint (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.2 2 =
    GlobalCarryRecognizer.enc (zQuad δ χ) (hdN (formulaTail (gRow t j).skel.formula)) from
      ((rn_dec_th _ _ _ hps).trans (by rw [hdN_of_cell htc])).trans (encC_eq _ _)] at hB
  rw [show decFingerprint (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.2 3 =
    GlobalCarryRecognizer.enc (zQuad δ χ) (tlN (formulaTail (gRow t j).skel.formula)) from
      ((rn_dec_tt _ _ _ hps).trans (by rw [tlN_of_cell htc])).trans (encC_eq _ _)] at hC'
  have hi := col_vI V χ αs hgen hnodes hsize j hj 0
  simp only [Fin.val_zero, zero_add, hk, Option.map_some, Option.getD_some] at hi
  exact export10_compress (b := V.basis) (E := envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j) _ _ (zQuad δ χ)
    (demT t).cells (formulaTail (gRow t j).skel.formula) hA hB hC' hi

include hnodes hsize hj hjn hsh hcell in
theorem row_rec6 (h6 : (gRow t j).skel.state = .s6) :
    FiniteIO.compress (coinsQ δ (gatherEnv V.basis (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j))
        (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j))
      (recValQ δ (gatherEnv V.basis (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j))
        (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j) ttRec) =
      FiniteIO.compress (m := 11) ⟨γC (δF := δ) χ, ρC (δF := δ) χ⟩
        (xReq δ (zQuad δ χ) (demT t).cells (formulaTail (formulaTail (gRow t j).skel.formula)) false) := by
  rw [row_coins V χ αs hgen j hj]
  obtain ⟨hk, htc⟩ := hsh.2.2.1 h6
  have hA := roleFP_dec V χ αs hgen (fun _ => 0) (fun _ => 0) hnodes hsize j hj hjn 3
  have hB := roleFP_dec V χ αs hgen (fun _ => 0) (fun _ => 0) hnodes hsize j hj hjn 4
  have hC' := roleFP_dec V χ αs hgen (fun _ => 0) (fun _ => 0) hnodes hsize j hj hjn 5
  have hps : (gRow t j).skel.state = .s2 ∨ (gRow t j).skel.state = .s5 ∨ (gRow t j).skel.state = .s6 ∨
      (gRow t j).skel.state = .s7 ∨ (gRow t j).skel.state = .s8 ∨ (gRow t j).skel.state = .s9 := Or.inr (Or.inr (Or.inl h6))
  rw [show decFingerprint (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.2 3 =
    GlobalCarryRecognizer.enc (zQuad δ χ) (formulaTail (formulaTail (gRow t j).skel.formula)) from
      (rn_dec_tt _ _ _ hps).trans (encC_eq _ _)] at hA
  rw [show decFingerprint (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.2 4 =
    GlobalCarryRecognizer.enc (zQuad δ χ) (hdN (formulaTail (formulaTail (gRow t j).skel.formula))) from
      ((rn_dec_tth _ _ _ h6).trans (by rw [hdN_of_cell htc])).trans (encC_eq _ _)] at hB
  rw [show decFingerprint (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.2 5 =
    GlobalCarryRecognizer.enc (zQuad δ χ) (tlN (formulaTail (formulaTail (gRow t j).skel.formula))) from
      ((rn_dec_ttt _ _ _ h6).trans (by rw [tlN_of_cell htc])).trans (encC_eq _ _)] at hC'
  have hi := col_vI V χ αs hgen hnodes hsize j hj 1
  simp only [Fin.val_one, hk, Option.map_some, Option.getD_some] at hi
  exact export10_compress (b := V.basis) (E := envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j) _ _ (zQuad δ χ)
    (demT t).cells (formulaTail (formulaTail (gRow t j).skel.formula)) hA hB hC' hi

include hnodes hsize hj hjn hsh hcell in
theorem row_recP0 (h0 : (gRow t j).skel.state = .s0) :
    FiniteIO.compress (coinsQ δ (gatherEnv V.basis (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j))
        (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j))
      (recValQ δ (gatherEnv V.basis (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j))
        (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j) op0PathRec) =
      FiniteIO.compress (m := 8) ⟨γC (δF := δ) χ, ρC (δF := δ) χ⟩
        (pReq δ (zQuad δ χ) (demT t).cells ((gRow t j).skel.subject, honestAx (gRow t j).skel)) := by
  rw [row_coins V χ αs hgen j hj]
  obtain ⟨hk, hslot⟩ := hsh.2.2.2.1 h0
  have hA := roleFP_pub V χ αs hgen (fun _ => 0) (fun _ => 0) hnodes hsize j hj hjn 0 (by simp)
    (Or.inr (Or.inl ⟨h0, Or.inl rfl⟩))
  have hB := roleFP_pub V χ αs hgen (fun _ => 0) (fun _ => 0) hnodes hsize j hj hjn 2 (by simp)
    (Or.inr (Or.inl ⟨h0, Or.inr rfl⟩))
  rw [show pubFingerprint (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.1 0 =
    GlobalCarryRecognizer.enc (zQuad δ χ) (gRow t j).skel.subject from
      (rn_pub_s _ _ _).trans (encC_eq _ _)] at hA
  rw [show pubFingerprint (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.1 2 =
    GlobalCarryRecognizer.enc (zQuad δ χ) (gRow t j).skel.evaluation from
      (rn_pub_e _ _ _).trans (encC_eq _ _)] at hB
  have hi := col_vI V χ αs hgen hnodes hsize j hj 0
  simp only [Fin.val_zero, zero_add, hk, Option.map_some, Option.getD_some] at hi
  congr 1
  exact path_vec (b := V.basis) (E := envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j) (zQuad δ χ)
    (demT t).cells _ _ _ (by rw [hslot]; rfl) hA hB (col_ax V χ αs hgen hnodes hsize j hj) hi

include hnodes hsize hj hjn hsh hcell in
theorem row_recP9 (h9 : (gRow t j).skel.state = .s9) :
    FiniteIO.compress (coinsQ δ (gatherEnv V.basis (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j))
        (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j))
      (recValQ δ (gatherEnv V.basis (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j))
        (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j) op9PathRec) =
      FiniteIO.compress (m := 8) ⟨γC (δF := δ) χ, ρC (δF := δ) χ⟩
        (pReq δ (zQuad δ χ) (demT t).cells
          (P8Census.skeletonSubformula (gRow t j).skel 0 .result, honestAx (gRow t j).skel)) := by
  rw [row_coins V χ αs hgen j hj]
  obtain ⟨hk, hslot⟩ := hsh.2.2.2.2 h9
  have hA := roleFP_pub V χ αs hgen (fun _ => 0) (fun _ => 0) hnodes hsize j hj hjn 5 (by simp)
    (Or.inr (Or.inr ⟨h9, Or.inl rfl⟩))
  have hB := roleFP_pub V χ αs hgen (fun _ => 0) (fun _ => 0) hnodes hsize j hj hjn 7 (by simp)
    (Or.inr (Or.inr ⟨h9, Or.inr rfl⟩))
  rw [show pubFingerprint (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.1 5 =
    GlobalCarryRecognizer.enc (zQuad δ χ) (P8Census.skeletonSubformula (gRow t j).skel 0 .result) from
      (rn_pub_sf1e _ _ _ h9).trans (encC_eq _ _)] at hA
  rw [show pubFingerprint (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.1 7 =
    GlobalCarryRecognizer.enc (zQuad δ χ) (P8Census.skeletonSubformula (gRow t j).skel 1 .formula) from
      (rn_pub_sf2f _ _ _ h9).trans (encC_eq _ _)] at hB
  have hi := col_vI V χ αs hgen hnodes hsize j hj 1
  simp only [Fin.val_one, hk, Option.map_some, Option.getD_some] at hi
  congr 1
  exact path_vec (b := V.basis) (E := envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) j) (zQuad δ χ)
    (demT t).cells _ _ _ (by rw [hslot]; rfl) hA hB (col_ax V χ αs hgen hnodes hsize j hj) hi

end RowFinal

theorem isPathAx_of_ne {a : ℕ} (h0 : a ≠ 0) (h1 : a ≠ 1) : isPathAx a = true := by
  have h2 : 2 ≤ a := by omega
  simp [isPathAx, depthOf, axisBits_of_two_le h2]

theorem slot_ne_zero {n r : Noun} {a : ℕ} (h : Noun.slot a n = some r) : a ≠ 0 := by
  rintro rfl
  simp [Noun.slot] at h

/-- The generator rows, re-indexed from `0`. -/
theorem flatMap_genRowsT {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] {δ : F}
    [Fact (¬ IsSquare (algebraMap F K δ))] {α : Type} (t : NTree (GenComputeRow (Quad (algebraMap F K δ))))
    (g : GenComputeRow (Quad (algebraMap F K δ)) → List α) :
    (genRowsT t).flatMap g = (List.range (nRows t)).flatMap fun j => g (gRow t j) := by
  simp only [genRowsT, gRow, List.range'_eq_map_range, List.map_map, List.flatMap_map]
  congr 1
  funext j
  simp only [Function.comp, Nat.add_comm]

theorem mem_preads {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] [DecidableEq F] {δ : F}
    [Fact (¬ IsSquare (algebraMap F K δ))] (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (j : ℕ)
    (hjn : j < nRows t) (r : Noun × ℕ) (hr : r ∈ rowPathKeys (gRow t j)) : r ∈ (demT t).preads := by
  show r ∈ (genRowsT t).flatMap rowPathKeys
  rw [flatMap_genRowsT]
  exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hjn, hr⟩

section RowFinal2
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [DecidableEq F] {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))] {hC : ℕ} {S : MemShape}
variable (V : VerifierData F K hC S) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ)) {fuel : ℕ}
  {subject formula : Noun} {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))} {result : Noun}
  (hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel subject formula = .ok (t, result))
  (hnodes : ∀ i : Fin V.N, V.computeNodes i = V.orbitC.ω ^ (i : ℕ)) (hsize : V.N ≤ 2 ^ hC)
  (j : ℕ) (hj : j < V.N) (hjn : j < nRows t)
  (hsh : RowShape (gRow t j)) (hcell : (gRow t j).skel.formula.isCell = true)

include hnodes hsize hj hjn hsh hcell in
/-- **`hrowP` at one row**: the path term of the honest row (accumulators zeroed) is the sum of the
reciprocals of the memory side's path-provide requests `pReq` of the row's path-kind keys. -/
theorem hrowP_row :
    termQ δ V.basis accSlotsPT accSlotsPImT (envAcc V χ αs hgen (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => 0) j) =
      (((rowPathKeys (gRow t j)).filter fun r => isPathAx r.2).map fun r =>
        (FiniteIO.compress (m := 8) ⟨γC (δF := δ) χ, ρC (δF := δ) χ⟩
          (pReq δ (zC (δF := δ) χ) (demT (F := F) (K := K) (δ := δ) t).cells r))⁻¹).sum := by
  have hz := col_z1 V χ αs hgen (fun _ => 0) (fun _ => 0) hnodes hsize j hj
  by_cases hax : honestAx (gRow t j).skel = 1
  · -- An axis-1 row: `z1 = 1`, the path term is `0`, and the row's path key `(·, 1)` is not a path read
    rw [termQ_PT_of_z1 δ V.basis _ (by rw [hz, if_pos hax])]
    have hn : ((rowPathKeys (gRow t j)).filter fun r => isPathAx r.2) = [] := by
      rw [List.filter_eq_nil_iff]
      intro r hr
      have h1 : (gRow t j).skel.state = .s0 → (rowSlotKeys (gRow t j))[1]? =
          some ((gRow t j).skel.subject, honestAx (gRow t j).skel) :=
        fun h0 => (hsh.2.2.2.1 h0).1
      have h2 : (gRow t j).skel.state = .s9 → (rowSlotKeys (gRow t j))[2]? =
          some (P8Census.skeletonSubformula (gRow t j).skel 0 .result, honestAx (gRow t j).skel) :=
        fun h9 => (hsh.2.2.2.2 h9).1
      rw [rowPathKeys_eq (gRow t j) _ _ h1 h2] at hr
      have hax1' : isPathAx 1 = false := by decide
      simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at hr
      rcases hr with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [hax, hax1']
    rw [hn]; rfl
  rw [termQ_PT_of_z0 δ V.basis _ (by rw [hz, if_neg hax])]
  have hsel := row_sel V χ αs hgen (fun _ => 0) (fun _ => 0) hnodes hsize j hj hjn
  rw [termQ_P_val δ V.basis _ (stT t j) hsel]
  obtain ⟨-, i1, i2⟩ := row_inv V χ αs hgen (fun _ => 0) (fun _ => 0) hnodes hsize j hj
  rw [i1, i2, den1Q_val δ _ _ (stT t j) hsel, den2Q_val δ _ _ (stT t j) hsel]
  obtain ⟨f1, f2, f3, f4⟩ := stT_facts (gRow t j).skel.state
  have e1 : (stT t j ∈ slot1ExportSels) = PS (gRow t j).skel.state := propext f1
  have e6 : (stT t j = 6) = ((gRow t j).skel.state = .s6) := propext f2
  have e0 : (stT t j = 0) = ((gRow t j).skel.state = .s0) := propext f3
  have e9 : (stT t j = 9) = ((gRow t j).skel.state = .s9) := propext f4
  simp only [e1, e6, e0, e9]
  have hP0 : ∀ h0 : (gRow t j).skel.state = .s0, ¬ PS (gRow t j).skel.state := fun h0 => by
    rw [h0]; decide
  have hP9 : ∀ h9 : (gRow t j).skel.state = .s9, (gRow t j).skel.state ≠ .s6 := fun h9 => by
    rw [h9]; decide
  have h1 : (gRow t j).skel.state = .s0 → (rowSlotKeys (gRow t j))[1]? =
      some ((gRow t j).skel.subject, honestAx (gRow t j).skel) ∧
      isPathAx (honestAx (gRow t j).skel) = true := by
    intro h0
    obtain ⟨hk, hslot⟩ := hsh.2.2.2.1 h0
    exact ⟨hk, isPathAx_of_ne (slot_ne_zero hslot) hax⟩
  have h2 : (gRow t j).skel.state = .s9 → (rowSlotKeys (gRow t j))[2]? =
      some (P8Census.skeletonSubformula (gRow t j).skel 0 .result, honestAx (gRow t j).skel) ∧
      isPathAx (honestAx (gRow t j).skel) = true := by
    intro h9
    obtain ⟨hk, hslot⟩ := hsh.2.2.2.2 h9
    exact ⟨hk, isPathAx_of_ne (slot_ne_zero hslot) hax⟩
  rw [rhsP_eq (gRow t j) _ _ _ h1 h2]
  by_cases a0 : (gRow t j).skel.state = .s0
  · have a9 : ¬ (gRow t j).skel.state = .s9 := fun h => by rw [a0] at h; cases h
    simp only [if_pos a0, if_neg a9, if_neg (hP0 a0), add_zero, zero_add]
    rw [row_recP0 V χ αs hgen hnodes hsize j hj hjn hsh hcell a0]
    rfl
  · by_cases a9 : (gRow t j).skel.state = .s9
    · simp only [if_neg a0, if_pos a9, if_neg (hP9 a9), add_zero, zero_add]
      rw [row_recP9 V χ αs hgen hnodes hsize j hj hjn hsh hcell a9]
      rfl
    · simp [a0, a9]

include hnodes hsize hj hjn hsh hcell in
/-- **`hrowX` at one row**: the export term of the honest row (accumulators zeroed) is the sum of the
reciprocals of the memory side's export requests `xReq` of the row's export-kind keys (`shallowSided`). -/
theorem hrowX_row :
    termQ δ V.basis accSlotsX accSlotsXIm (envAcc V χ αs hgen (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => 0) j) =
      ((shallowSided (rowExportKeys (gRow t j))).map fun c =>
        (FiniteIO.compress (m := 11) ⟨γC (δF := δ) χ, ρC (δF := δ) χ⟩
          (xReq δ (zC (δF := δ) χ) (demT (F := F) (K := K) (δ := δ) t).cells c.1 c.2))⁻¹).sum := by
  have hsel := row_sel V χ αs hgen (fun _ => 0) (fun _ => 0) hnodes hsize j hj hjn
  rw [termQ_X_val δ V.basis _ (stT t j) hsel]
  obtain ⟨i0, i1, i2⟩ := row_inv V χ αs hgen (fun _ => 0) (fun _ => 0) hnodes hsize j hj
  rw [i0, i1, i2, den1Q_val δ _ _ (stT t j) hsel, den2Q_val δ _ _ (stT t j) hsel]
  obtain ⟨f1, f2, f3, f4⟩ := stT_facts (gRow t j).skel.state
  have e1 : (stT t j ∈ slot1ExportSels) = PS (gRow t j).skel.state := propext f1
  have e6 : (stT t j = 6) = ((gRow t j).skel.state = .s6) := propext f2
  have e0 : (stT t j = 0) = ((gRow t j).skel.state = .s0) := propext f3
  have e9 : (stT t j = 9) = ((gRow t j).skel.state = .s9) := propext f4
  simp only [e1, e6, e0, e9]
  have hs0PS : ∀ h0 : (gRow t j).skel.state = .s0, ¬ PS (gRow t j).skel.state := fun h0 => by
    rw [h0]; decide
  have h9PS : ∀ h9 : (gRow t j).skel.state = .s9, ¬ (gRow t j).skel.state = .s6 := fun h9 => by
    rw [h9]; decide
  have hs6PS : ∀ h6 : (gRow t j).skel.state = .s6, PS (gRow t j).skel.state := fun h6 => by
    rw [h6]; decide
  have hpsl : PS (gRow t j).skel.state → (rowSlotKeys (gRow t j))[1]? =
      some (formulaTail (gRow t j).skel.formula, 2) ∧ (formulaTail (gRow t j).skel.formula).isCell = true :=
    fun h => hsh.2.1 (by rcases h with h | h | h | h | h | h <;> simp [h])
  have hhead : (rowSlotKeys (gRow t j))[0]? = some ((gRow t j).skel.formula, 3) := by
    obtain ⟨-, -, hh⟩ := gRow_facts hgen j hjn
    rcases hk : rowSlotKeys (gRow t j) with _ | ⟨x, xs⟩
    · rw [hk] at hh; simp at hh
    · rw [hk] at hh; simp at hh; simp [hh]
  have h6sl := hsh.2.2.1
  rw [rhsX_eq (gRow t j) _ (formulaTail (gRow t j).skel.formula)
    (formulaTail (formulaTail (gRow t j).skel.formula))
    (fun c b => (FiniteIO.compress (m := 11) ⟨γC (δF := δ) χ, ρC (δF := δ) χ⟩
      (xReq δ (zC (δF := δ) χ) (demT (F := F) (K := K) (δ := δ) t).cells c b))⁻¹) hhead hcell hpsl h6sl]
  rw [row_den0 V χ αs hgen hnodes hsize j hj hjn hsh hcell]
  show _ = _ + (_ + _)
  have hz : zC (δF := δ) χ = zQuad δ χ := rfl
  simp only [hz]
  by_cases hP : PS (gRow t j).skel.state <;> by_cases h6 : (gRow t j).skel.state = .s6
  · have a0 : ¬ (gRow t j).skel.state = .s0 := fun h => hs0PS h hP
    have a9 : ¬ (gRow t j).skel.state = .s9 := fun h => by rw [h6] at h; cases h
    simp only [if_pos hP, if_pos h6, if_neg a0, if_neg a9, zero_add, add_zero]
    rw [row_rec1 V χ αs hgen hnodes hsize j hj hjn hsh hcell hP,
      row_rec6 V χ αs hgen hnodes hsize j hj hjn hsh hcell h6]
    ring
  · have a0 : ¬ (gRow t j).skel.state = .s0 := fun h => hs0PS h hP
    simp only [if_pos hP, if_neg h6, if_neg a0, zero_add, add_zero]
    rw [row_rec1 V χ αs hgen hnodes hsize j hj hjn hsh hcell hP]
  · exact absurd (hs6PS h6) hP
  · simp only [if_neg hP, if_neg h6, zero_add, add_zero]

include hnodes hsize in
/-- **`hrowX`, as a theorem**: at every row `j < N` of the honest
trace with the accumulators zeroed, the export term is the sum of the reciprocals of the memory side's export
requests `xReq` of the row's export-kind keys, one per occurrence. -/
theorem hrowX_T (hN : V.N = nRows t) (χ : Coins frameVCL K) (j : ℕ) (hj : j < V.N) :
    termQ δ V.basis accSlotsX accSlotsXIm
        (envAcc V χ αs hgen (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => 0) j) =
      ((shallowSided (rowExportKeys (gRow t j))).map fun c =>
        (FiniteIO.compress (m := 11) ⟨γC (δF := δ) χ, ρC (δF := δ) χ⟩
          (xReq δ (zC (δF := δ) χ) (demT (F := F) (K := K) (δ := δ) t).cells c.1 c.2))⁻¹).sum := by
  have hjn : j < nRows t := hN ▸ hj
  obtain ⟨hsh, hcell, -⟩ := gRow_facts hgen j hjn
  exact hrowX_row V χ αs hgen hnodes hsize j hj hjn hsh hcell

include hnodes hsize in
/-- **`hrowP`, as a theorem**: the same for the path term and `pReq`; the depth-0
axis `1` is the only path read the memory side drops (`isPathAx`), and it is exactly the rows the honest trace
fills `z1 = 1`, where the tower-local path term is `0`. -/
theorem hrowP_T (hN : V.N = nRows t)
    (χ : Coins frameVCL K) (j : ℕ) (hj : j < V.N) :
    termQ δ V.basis accSlotsPT accSlotsPImT
        (envAcc V χ αs hgen (fun _ => (0 : Quad (algebraMap F K δ))) (fun _ => 0) j) =
      (((rowPathKeys (gRow t j)).filter fun r => isPathAx r.2).map fun r =>
        (FiniteIO.compress (m := 8) ⟨γC (δF := δ) χ, ρC (δF := δ) χ⟩
          (pReq δ (zC (δF := δ) χ) (demT (F := F) (K := K) (δ := δ) t).cells r))⁻¹).sum := by
  have hjn : j < nRows t := hN ▸ hj
  obtain ⟨hsh, hcell, -⟩ := gRow_facts hgen j hjn
  exact hrowP_row V χ αs hgen hnodes hsize j hj hjn hsh hcell

include hnodes hsize hj hjn hsh in
/-- **The `z1` gates hold at every honest row** (any accumulator filling): `z1 = [axis = 1]` is boolean,
`z1·(ax − 1) = 0`, and at an axis-1 `s0` / `s9` row the OP0 result is the subject (`slot 1 n = n`) and the OP9 arm
is the core, so the path record's child fingerprint equals its root fingerprint (`z1·s0·(e − s)`,
`z1·s9·(sf2_f − sf1_e)`).  No bad event: the equalities are of fingerprints of EQUAL nouns. -/
theorem z1Gates_row (accX accP : ℕ → Quad (algebraMap F K δ)) :
    ∀ g ∈ z1Gates V.basis δ, g.eval (envAcc V χ αs hgen accX accP j) = 0 := by
  set E := envAcc V χ αs hgen accX accP j with hE
  have hz : E.trace z1Col = if honestAx (gRow t j).skel = 1 then 1 else 0 :=
    col_z1 V χ αs hgen accX accP hnodes hsize j hj
  have hax : E.trace axCol = ((honestAx (gRow t j).skel : ℕ) : F) :=
    col_axF V χ αs hgen accX accP hnodes hsize j hj
  have hsel := row_sel V χ αs hgen accX accP hnodes hsize j hj hjn
  obtain ⟨-, -, f3, f4⟩ := stT_facts (gRow t j).skel.state
  have key : ∀ (sel : ℕ) (r : Fin 8 → Entry) (c : Fin 3),
      (E.trace z1Col * E.trace sel = 0 ∨
        Q.val δ (entryQ F (r ⟨3 + (c : ℕ), by omega⟩)) (gatherEnv V.basis E) E =
          Q.val δ (entryQ F (r ⟨(c : ℕ), by omega⟩)) (gatherEnv V.basis E) E) →
      ∀ g ∈ qGates V.basis (z1EqQ F δ sel r c), g.eval E = 0 := by
    intro sel r c h
    refine (qGates_iff V.basis (isCoordEnv_gather V.basis E) _).mpr ((Q.isZero_iff δ _ E _).mpr ?_)
    rw [z1EqQ, qmul_val, qlift_val, qsub_val]
    rcases h with h | h
    · simp only [CoeffExpr.eval, selVar, h, map_zero, zero_mul]
    · rw [h, sub_self, mul_zero]
  have pathEq : ∀ {rr cc axc idx : ℕ} {A B : FP (Quad (algebraMap F K δ))} (c : Fin 3),
      RoleFP δ V.basis E rr A → RoleFP δ V.basis E cc B → A = B →
      Q.val δ (entryQ F ((pathRec rr cc axc idx) ⟨3 + (c : ℕ), by omega⟩)) (gatherEnv V.basis E) E =
        Q.val δ (entryQ F ((pathRec rr cc axc idx) ⟨(c : ℕ), by omega⟩)) (gatherEnv V.basis E) E := by
    intro rr cc axc idx A B c hA hB hAB
    subst hAB
    fin_cases c
    · exact (hB 0).trans (hA 0).symm
    · exact (hB 1).trans (hA 1).symm
    · exact (hB 2).trans (hA 2).symm
  have slot1' : ∀ n : Noun, Noun.slot 1 n = some n := fun n => by simp [Noun.slot]
  intro g hg
  simp only [z1Gates, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap] at hg
  rcases hg with ((rfl | rfl) | ⟨c, -, hg⟩) | ⟨c, -, hg⟩
  · simp only [z1BoolGate, CoeffExpr.eval, hz]
    by_cases h : honestAx (gRow t j).skel = 1 <;> simp [h]
  · simp only [z1AxGate, CoeffExpr.eval, hz, hax]
    by_cases h : honestAx (gRow t j).skel = 1 <;> simp [h]
  · refine key 0 op0PathRec c ?_ g hg
    by_cases h1 : honestAx (gRow t j).skel = 1
    · by_cases h0 : (gRow t j).skel.state = .s0
      · right
        obtain ⟨hk, hslot⟩ := hsh.2.2.2.1 h0
        have hA := roleFP_pub V χ αs hgen accX accP hnodes hsize j hj hjn 0 (by simp)
          (Or.inr (Or.inl ⟨h0, Or.inl rfl⟩))
        have hB := roleFP_pub V χ αs hgen accX accP hnodes hsize j hj hjn 2 (by simp)
          (Or.inr (Or.inl ⟨h0, Or.inr rfl⟩))
        rw [show pubFingerprint (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.1 0 =
          GlobalCarryRecognizer.enc (zQuad δ χ) (gRow t j).skel.subject from
            (rn_pub_s _ _ _).trans (encC_eq _ _)] at hA
        rw [show pubFingerprint (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.1 2 =
          GlobalCarryRecognizer.enc (zQuad δ χ) (gRow t j).skel.evaluation from
            (rn_pub_e _ _ _).trans (encC_eq _ _)] at hB
        rw [h1, slot1'] at hslot
        have hev : (gRow t j).skel.evaluation = (gRow t j).skel.subject :=
          (Option.some.inj hslot).symm
        exact pathEq (axc := axCol) (idx := vIdxCol 0) c hA hB (by rw [hev])
      · left
        rw [hsel 0 (by norm_num)]
        have : ¬ (0 = stT t j) := fun h => h0 (f3.mp h.symm)
        simp [this]
    · left; rw [hz, if_neg h1]; simp
  · refine key 9 op9PathRec c ?_ g hg
    by_cases h1 : honestAx (gRow t j).skel = 1
    · by_cases h9 : (gRow t j).skel.state = .s9
      · right
        obtain ⟨hk, hslot⟩ := hsh.2.2.2.2 h9
        have hA := roleFP_pub V χ αs hgen accX accP hnodes hsize j hj hjn 5 (by simp)
          (Or.inr (Or.inr ⟨h9, Or.inl rfl⟩))
        have hB := roleFP_pub V χ αs hgen accX accP hnodes hsize j hj hjn 7 (by simp)
          (Or.inr (Or.inr ⟨h9, Or.inr rfl⟩))
        rw [show pubFingerprint (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.1 5 =
          GlobalCarryRecognizer.enc (zQuad δ χ) (P8Census.skeletonSubformula (gRow t j).skel 0 .result) from
            (rn_pub_sf1e _ _ _ h9).trans (encC_eq _ _)] at hA
        rw [show pubFingerprint (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.1 7 =
          GlobalCarryRecognizer.enc (zQuad δ χ) (P8Census.skeletonSubformula (gRow t j).skel 1 .formula) from
            (rn_pub_sf2f _ _ _ h9).trans (encC_eq _ _)] at hB
        rw [h1, slot1'] at hslot
        have hev : P8Census.skeletonSubformula (gRow t j).skel 1 .formula =
            P8Census.skeletonSubformula (gRow t j).skel 0 .result := (Option.some.inj hslot).symm
        exact pathEq (axc := axCol) (idx := vIdxCol 1) c hA hB (by rw [hev])
      · left
        rw [hsel 9 (by norm_num)]
        have : ¬ (9 = stT t j) := fun h => h9 (f4.mp h.symm)
        simp [this]
    · left; rw [hz, if_neg h1]; simp

end RowFinal2

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
