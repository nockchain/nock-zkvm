/-
  Nock/NockVMROM/Thm54/VclL/Handle/WalkTeleJ8.lean

  New module, additive.

  The path telescope of `walkChipHQ` (`TeleHQ.walkHQ_telescopeP`, `PathVSQ.walk_provs_sumQ`) re-proved on the
  ternary-kind twin `walkChipHQK` (its mixed gates and column layout are `walkChipHQ`'s, `walkHQK_unchanged`;
  only the two kind gates differ), then carried to `walkChipJ8` through `bitFix` (which touches only the
  certificate columns `14..20`):

  * `walkHQK_qgates`, `walkHQK_inv`, `walkHQK_masks`, **`walkHQK_telescopeP`**, `walkHQK_provs_sumQ`;
  * `walkPProvs_bitFix` (the provider list of `bitFix Q` is the committed trace's);
  * **`walkJ8_provs_sumQ`**: the providers `ServeH.walkPProvs … Q` of an accepted `walkChipJ8` trace, weighted
    by `mL / mR`, sum at the handle coins `(γH′, ρH′)` to the terminal `(pub₆, pub₇)` — the `T_prov.p` of
    `GoodCJ8` — and `walkJ8_provs_denQ` (their denominators are nonzero).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8
import Nock.NockVMROM.Thm54.VclL.Handle.PathVSQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Handle.WalkTeleJ8

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ
open Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ Nock.NockVMROM.Thm54.VclL.Handle.PathVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceVSQ (mcoins)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8
open Module
open scoped Polynomial

noncomputable section

section Walk
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kroots : ℕ)
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

local notation "𝕂′" => Quad (algebraMap F K δF)

section HQK
variable (Q : Fin (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.w → F[X])

theorem walkHQK_qgates (hsat : (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    ∀ e ∈ WalkHQ.gatesQ δF,
      e.ev δF (qwEK δF kroots b nodes orbit chals pubs Q i) (qwEF b nodes orbit chals pubs Q i) = 0 := by
  have hl := (expandChip_satisfies_iff_language (walkTemplateHQK δF kroots) b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)
  intro e he
  exact ev_eq_zero_of_gates δF _ _ e fun g hg =>
    hl.2.2.2 g (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hg⟩))

/-- **The three `𝕂′` walk inverses** on the ternary-kind twin. -/
theorem walkHQK_inv (hsat : (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    (wDenQ δF kroots b nodes orbit chals pubs Q WalkHC.xKeyH i ≠ 0 ∧
      wQ δF kroots b nodes orbit chals pubs Q WalkHQ.hxInvQ i = (wDenQ δF kroots b nodes orbit chals pubs Q WalkHC.xKeyH i)⁻¹) ∧
    (wDenQ δF kroots b nodes orbit chals pubs Q WalkHC.recLH i ≠ 0 ∧
      wQ δF kroots b nodes orbit chals pubs Q WalkHQ.hpInvLQ i = (wDenQ δF kroots b nodes orbit chals pubs Q WalkHC.recLH i)⁻¹) ∧
    (wDenQ δF kroots b nodes orbit chals pubs Q WalkHC.recRH i ≠ 0 ∧
      wQ δF kroots b nodes orbit chals pubs Q WalkHQ.hpInvRQ i = (wDenQ δF kroots b nodes orbit chals pubs Q WalkHC.recRH i)⁻¹) := by
  have hg := walkHQK_qgates δF kroots b hn nodes orbit chals pubs Q hsat i
  refine ⟨inv_of_gate δF ?_, inv_of_gate δF ?_, inv_of_gate δF ?_⟩
  · have g := hg _ (by simp [WalkHQ.gatesQ] : QE.sub (QE.mul δF (QE.var WalkHQ.hxInvQ) (HQ.denKeyQ δF WalkHC.xKeyH))
      QE.one ∈ WalkHQ.gatesQ δF)
    rwa [ev_sub, ev_mul, ev_var, ev_one] at g
  · have g := hg _ (by simp [WalkHQ.gatesQ] : QE.sub (QE.mul δF (QE.var WalkHQ.hpInvLQ) (HQ.denKeyQ δF WalkHC.recLH))
      QE.one ∈ WalkHQ.gatesQ δF)
    rwa [ev_sub, ev_mul, ev_var, ev_one] at g
  · have g := hg _ (by simp [WalkHQ.gatesQ] : QE.sub (QE.mul δF (QE.var WalkHQ.hpInvRQ) (HQ.denKeyQ δF WalkHC.recRH))
      QE.one ∈ WalkHQ.gatesQ δF)
    rwa [ev_sub, ev_mul, ev_var, ev_one] at g

theorem walkHQK_masks (hbind : (walkChipHQK δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (qwEF b nodes orbit chals pubs Q i).trace WChip.isF = (if (i : ℕ) = 0 then 1 else 0) ∧
      (qwEF b nodes orbit chals pubs Q i).trace WChip.isL = (if (i : ℕ) = n - 1 then 1 else 0) := by
  have hw : (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.w = 166 :=
    walkChipHQK_width δF kroots b hn nodes orbit chals pubs
  have h0 : Q ⟨0, by rw [hw]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 3; omega⟩
  have h1 : Q ⟨1, by rw [hw]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 3; omega⟩
  exact masks_of hn nodes orbit Q _ _ h0 h1 hinj _ _ i

theorem qwEKK_pub (i : Fin n) (idx : ℕ) : (qwEK δF kroots b nodes orbit chals pubs Q i).pub idx = pubs idx :=
  gather_pub_T b (walkTemplateHQ δF kroots) 25 (walkTemplateHQ_baseCols δF kroots) _ pubs rfl idx

theorem qwEKK_chal (i : Fin n) (idx : ℕ) : (qwEK δF kroots b nodes orbit chals pubs Q i).chal idx = chals idx :=
  gather_chal_T b (walkTemplateHQ δF kroots) 25 (walkTemplateHQ_baseCols δF kroots) _ chals rfl idx

theorem qwEFK_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (j : ℕ) :
    (qwEF b nodes orbit chals pubs Q i).traceNext j = (qwEF b nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩).trace j :=
  traceNext_eq nodes orbit Q _ _ hadj i hi j

theorem qwEKK_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (r : ℕ) :
    (qwEK δF kroots b nodes orbit chals pubs Q i).traceNext r =
      (qwEK δF kroots b nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩).trace r :=
  gather_next_T b _ _ _ (qwEFK_next δF kroots b hn nodes orbit chals pubs Q hadj i hi) r

/-- **The `𝕂′` walk path telescope on `walkChipHQK`**: `Σ_i (mL · invL′ + mR · invR′) = (pub₆, pub₇)`. -/
theorem walkHQK_telescopeP (hsat : (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipHQK δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ i, wPTermQ δF kroots b nodes orbit chals pubs Q i =
      Quad.mk _ (pubs WalkHQ.pubPQ) (pubs (WalkHQ.pubPQ + 1)) := by
  have hg := walkHQK_qgates δF kroots b hn nodes orbit chals pubs Q hsat
  refine qTelescope δF hn (fun i => (qwEF b nodes orbit chals pubs Q i).trace WChip.isF)
    (fun i => (qwEF b nodes orbit chals pubs Q i).trace WChip.isL)
    (fun i => wQ δF kroots b nodes orbit chals pubs Q WalkHQ.hpAccQ i) _ _
    (fun i => (walkHQK_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj i).1)
    (fun i => (walkHQK_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj i).2) ?_ ?_ ?_
  · intro i
    have g := hg i _ (by simp [WalkHQ.gatesQ] : QE.scale (cv WChip.isF) (QE.sub (QE.var WalkHQ.hpAccQ)
      (WalkHQ.pTermQ true)) ∈ WalkHQ.gatesQ δF)
    simp only [WalkHQ.pTermQ, if_true, ev_scale, ev_sub, ev_add, ev_var] at g
    simpa only [cv, CoeffExpr.eval] using g
  · intro i hi
    have g := hg i _ (by simp [WalkHQ.gatesQ] : QE.scale (notE (cv WChip.isL)) (QE.sub (QE.sub (QE.next WalkHQ.hpAccQ)
      (QE.var WalkHQ.hpAccQ)) (WalkHQ.pTermQ false)) ∈ WalkHQ.gatesQ δF)
    simp only [WalkHQ.pTermQ, Bool.false_eq_true, if_false, ev_scale, ev_sub, ev_add, ev_var, ev_next] at g
    simp only [notE, cv, nv, CoeffExpr.eval, qwEKK_next δF kroots b hn nodes orbit chals pubs Q hadj i hi,
      qwEFK_next δF kroots b hn nodes orbit chals pubs Q hadj i hi] at g
    simpa only [wPTermQ, wQ, liftQ, map_sub, map_one] using g
  · intro i
    have g := hg i _ (by simp [WalkHQ.gatesQ] : QE.scale (cv WChip.isL) (QE.sub (QE.var WalkHQ.hpAccQ)
      (QE.pub WalkHQ.pubPQ)) ∈ WalkHQ.gatesQ δF)
    rw [ev_scale, ev_sub, ev_var, ev_pub, qwEKK_pub, qwEKK_pub] at g
    simpa only [cv, CoeffExpr.eval] using g

theorem wDenQK_eq4 (l : List (CoeffExpr F)) (hl : l.length ≤ 5) (i : Fin n) :
    wDenQ δF kroots b nodes orbit chals pubs Q l i =
      compress (mcoins δF chals)
        (liftRec (K := K) (L := 𝕂′) (ServeH.keyVec5 l (qwEF b nodes orbit chals pubs Q i))) := by
  rw [wDenQ, denKeyQ_ev' δF _ _ _ hl]
  simp only [coinsQ, qwEKK_chal]

theorem walkHQK_provs_denQ (hsat : (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) :
    ∀ q ∈ ServeH.walkPProvs b nodes orbit chals pubs Q,
      compress (mcoins δF chals) (BalanceQ.liftRec (L := 𝕂′) q.1) ≠ 0 := by
  intro q hq
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hq
  have hi := walkHQK_inv δF kroots b hn nodes orbit chals pubs Q hsat j
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · rw [← wDenQK_eq4 δF kroots b hn nodes orbit chals pubs Q _ (by simp [WalkHC.recLH])]; exact hi.2.1.1
  · rw [← wDenQK_eq4 δF kroots b hn nodes orbit chals pubs Q _ (by simp [WalkHC.recRH])]; exact hi.2.2.1

/-- **The `walkChipHQK` providers, weighted, sum to the terminal `(pub₆, pub₇)`.** -/
theorem walkHQK_provs_sumQ (hsat : (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipHQK δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ((ServeH.walkPProvs b nodes orbit chals pubs Q).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (mcoins δF chals) (BalanceQ.liftRec (L := 𝕂′) q.1))⁻¹).sum =
      Quad.mk _ (pubs WalkHQ.pubPQ) (pubs (WalkHQ.pubPQ + 1)) := by
  rw [← walkHQK_telescopeP δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj]
  simp only [ServeH.walkPProvs, map_flatMap_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, Function.comp_def]
  rw [Chips.ChipRAP.sum_finRange]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hi := walkHQK_inv δF kroots b hn nodes orbit chals pubs Q hsat j
  rw [wPTermQ, hi.2.1.2, hi.2.2.2, wDenQK_eq4 δF kroots b hn nodes orbit chals pubs Q _ (by simp [WalkHC.recLH]),
    wDenQK_eq4 δF kroots b hn nodes orbit chals pubs Q _ (by simp [WalkHC.recRH])]

/-- **The `𝕂′` walk export telescope on `walkChipHQK`**: `Σ_i invX′ᵢ = (pub₄, pub₅)`. -/
theorem walkHQK_telescopeX (hsat : (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipHQK δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ i, wQ δF kroots b nodes orbit chals pubs Q WalkHQ.hxInvQ i =
      Quad.mk _ (pubs WalkHQ.pubXQ) (pubs (WalkHQ.pubXQ + 1)) := by
  have hg := walkHQK_qgates δF kroots b hn nodes orbit chals pubs Q hsat
  refine qTelescope δF hn (fun i => (qwEF b nodes orbit chals pubs Q i).trace WChip.isF)
    (fun i => (qwEF b nodes orbit chals pubs Q i).trace WChip.isL)
    (fun i => wQ δF kroots b nodes orbit chals pubs Q WalkHQ.hxAccQ i) _ _
    (fun i => (walkHQK_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj i).1)
    (fun i => (walkHQK_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj i).2) ?_ ?_ ?_
  · intro i
    have g := hg i _ (by simp [WalkHQ.gatesQ] : QE.scale (cv WChip.isF) (QE.sub (QE.var WalkHQ.hxAccQ)
      (QE.var WalkHQ.hxInvQ)) ∈ WalkHQ.gatesQ δF)
    rw [ev_scale, ev_sub, ev_var, ev_var] at g
    simpa only [cv, CoeffExpr.eval] using g
  · intro i hi
    have g := hg i _ (by simp [WalkHQ.gatesQ] : QE.scale (notE (cv WChip.isL)) (QE.sub (QE.sub (QE.next WalkHQ.hxAccQ)
      (QE.var WalkHQ.hxAccQ)) (QE.next WalkHQ.hxInvQ)) ∈ WalkHQ.gatesQ δF)
    rw [ev_scale, ev_sub, ev_sub, ev_next, ev_var, ev_next] at g
    simp only [notE, cv, CoeffExpr.eval, qwEKK_next δF kroots b hn nodes orbit chals pubs Q hadj i hi] at g
    simpa only [wQ, liftQ, map_sub, map_one] using g
  · intro i
    have g := hg i _ (by simp [WalkHQ.gatesQ] : QE.scale (cv WChip.isL) (QE.sub (QE.var WalkHQ.hxAccQ)
      (QE.pub WalkHQ.pubXQ)) ∈ WalkHQ.gatesQ δF)
    rw [ev_scale, ev_sub, ev_var, ev_pub, qwEKK_pub, qwEKK_pub] at g
    simpa only [cv, CoeffExpr.eval] using g

theorem walkHQK_reqs_denQ (hsat : (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) :
    ∀ r ∈ ServeH.walkXReqs b nodes orbit chals pubs Q,
      compress (mcoins δF chals) (BalanceQ.liftRec (L := 𝕂′) r) ≠ 0 := by
  intro r hr
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hr
  rw [← wDenQK_eq4 δF kroots b hn nodes orbit chals pubs Q _ (by simp [WalkHC.xKeyH])]
  exact (walkHQK_inv δF kroots b hn nodes orbit chals pubs Q hsat j).1.1

/-- **The `walkChipHQK` export consumes sum to the terminal `(pub₄, pub₅)`.** -/
theorem walkHQK_reqs_sumQ (hsat : (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipHQK δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ((ServeH.walkXReqs b nodes orbit chals pubs Q).map fun r =>
        (compress (mcoins δF chals) (BalanceQ.liftRec (L := 𝕂′) r))⁻¹).sum =
      Quad.mk _ (pubs WalkHQ.pubXQ) (pubs (WalkHQ.pubXQ + 1)) := by
  rw [← walkHQK_telescopeX δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj]
  simp only [ServeH.walkXReqs, List.map_map, Function.comp_def]
  rw [Chips.ChipRAP.sum_finRange]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(walkHQK_inv δF kroots b hn nodes orbit chals pubs Q hsat j).1.2,
    wDenQK_eq4 δF kroots b hn nodes orbit chals pubs Q _ (by simp [WalkHC.xKeyH])]

end HQK

section J8
variable [DecidableEq F] [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (Q : Fin (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.w → F[X])

/-- `bitFix` leaves the provider list unchanged (it touches only the certificate columns `14..20`). -/
theorem walkPProvs_bitFix :
    ServeH.walkPProvs b nodes orbit chals pubs (bitFix δF kroots b hn nodes orbit chals pubs Q) =
      ServeH.walkPProvs b nodes orbit chals pubs Q := by
  have hw1 := walkChipHQK_width δF kroots b hn nodes orbit chals pubs
  have hw2 := walkChipJ8_width δF kroots b hn nodes orbit chals pubs
  have ht : ∀ (j : Fin n) (c : ℕ), c < 14 ∨ 21 ≤ c →
      (TeleH.wEF b nodes orbit chals pubs (bitFix δF kroots b hn nodes orbit chals pubs Q) j).trace c =
        (TeleH.wEF b nodes orbit chals pubs Q j).trace c := by
    intro j c hc
    simp only [TeleH.wEF, Reify.envOfTrace]
    by_cases hc' : c < 166
    · rw [dif_pos (by rw [hw1]; exact hc'), dif_pos (by rw [hw2]; exact hc'),
        bitFix_off δF kroots b hn nodes orbit chals pubs Q ⟨c, by rw [hw1]; exact hc'⟩ hc]
    · rw [dif_neg (by rw [hw1]; exact hc'), dif_neg (by rw [hw2]; exact hc')]
  unfold ServeH.walkPProvs
  congr 1
  funext j
  have hk : ∀ l : List (CoeffExpr F), l = WalkHC.recLH ∨ l = WalkHC.recRH →
      ServeH.keyVec5 (K := K) l (TeleH.wEF b nodes orbit chals pubs (bitFix δF kroots b hn nodes orbit chals pubs Q) j) =
        ServeH.keyVec5 l (TeleH.wEF b nodes orbit chals pubs Q j) := by
    intro l hl
    funext k
    rcases hl with rfl | rfl <;> fin_cases k <;>
      simp [ServeH.keyVec5, WalkHC.recLH, WalkHC.recRH, CoeffExpr.eval, cv,
        ht j WChip.ridx (by decide), ht j WChip.pre (by decide), ht j WalkHC.kL (by decide),
        ht j WalkHC.vL (by decide), ht j WalkHC.kR (by decide), ht j WalkHC.vR (by decide)]
  rw [hk _ (Or.inl rfl), hk _ (Or.inr rfl), ht j WChip.mL (by decide), ht j WChip.mR (by decide)]

variable (hsat : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
  (hbind : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
  (hF : GeneratedField.PrimeFieldElems F) (hp : 64 ≤ ringChar F)

include hsat hbind hF hp in
/-- **`T_prov.p`**: the providers of an accepted `walkChipJ8` trace (committed `Q`), weighted by `mL / mR`, sum
at the handle coins to the terminal `(pub₆, pub₇)`. -/
theorem walkJ8_provs_sumQ (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ((ServeH.walkPProvs b nodes orbit chals pubs Q).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (mcoins δF chals) (BalanceQ.liftRec (L := 𝕂′) q.1))⁻¹).sum =
      Quad.mk _ (pubs WalkHQ.pubPQ) (pubs (WalkHQ.pubPQ + 1)) := by
  obtain ⟨hs, hb⟩ := walkChipJ8_to_HQK δF kroots b hn nodes orbit chals pubs Q hsat hbind hF hp
  rw [← walkPProvs_bitFix]
  exact walkHQK_provs_sumQ δF kroots b hn nodes orbit chals pubs _ hs hb hinj hadj

include hsat hbind hF hp in
theorem walkJ8_provs_denQ :
    ∀ q ∈ ServeH.walkPProvs b nodes orbit chals pubs Q,
      compress (mcoins δF chals) (BalanceQ.liftRec (L := 𝕂′) q.1) ≠ 0 := by
  obtain ⟨hs, -⟩ := walkChipJ8_to_HQK δF kroots b hn nodes orbit chals pubs Q hsat hbind hF hp
  rw [← walkPProvs_bitFix]
  exact walkHQK_provs_denQ δF kroots b hn nodes orbit chals pubs _ hs

/-- `bitFix` leaves the consumed export keys unchanged. -/
theorem walkXReqs_bitFix :
    ServeH.walkXReqs (K := K) b nodes orbit chals pubs (bitFix δF kroots b hn nodes orbit chals pubs Q) =
      ServeH.walkXReqs b nodes orbit chals pubs Q := by
  have hw1 := walkChipHQK_width δF kroots b hn nodes orbit chals pubs
  have hw2 := walkChipJ8_width δF kroots b hn nodes orbit chals pubs
  have ht : ∀ (j : Fin n) (c : ℕ), c < 14 ∨ 21 ≤ c →
      (TeleH.wEF b nodes orbit chals pubs (bitFix δF kroots b hn nodes orbit chals pubs Q) j).trace c =
        (TeleH.wEF b nodes orbit chals pubs Q j).trace c := by
    intro j c hc
    simp only [TeleH.wEF, Reify.envOfTrace]
    by_cases hc' : c < 166
    · rw [dif_pos (by rw [hw1]; exact hc'), dif_pos (by rw [hw2]; exact hc'),
        bitFix_off δF kroots b hn nodes orbit chals pubs Q ⟨c, by rw [hw1]; exact hc'⟩ hc]
    · rw [dif_neg (by rw [hw1]; exact hc'), dif_neg (by rw [hw2]; exact hc')]
  unfold ServeH.walkXReqs
  congr 1
  funext j
  funext k
  fin_cases k <;>
    simp [ServeH.keyVec5, WalkHC.xKeyH, CoeffExpr.eval, cv,
      ht j WChip.idx (by decide), ht j WalkHC.kL (by decide),
      ht j WalkHC.vL (by decide), ht j WalkHC.kR (by decide), ht j WalkHC.vR (by decide)]

include hsat hbind hF hp in
/-- **The walk-instance-1 share of `T_ext.x`**: the export keys an accepted `walkChipJ8` trace consumes sum at the
handle coins to its terminal `(pub₄, pub₅)`. -/
theorem walkJ8_reqs_sumQ (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ((ServeH.walkXReqs b nodes orbit chals pubs Q).map fun r =>
        (compress (mcoins δF chals) (BalanceQ.liftRec (L := 𝕂′) r))⁻¹).sum =
      Quad.mk _ (pubs WalkHQ.pubXQ) (pubs (WalkHQ.pubXQ + 1)) := by
  obtain ⟨hs, hb⟩ := walkChipJ8_to_HQK δF kroots b hn nodes orbit chals pubs Q hsat hbind hF hp
  rw [← walkXReqs_bitFix]
  exact walkHQK_reqs_sumQ δF kroots b hn nodes orbit chals pubs _ hs hb hinj hadj

include hsat hbind hF hp in
theorem walkJ8_reqs_denQ :
    ∀ r ∈ ServeH.walkXReqs b nodes orbit chals pubs Q,
      compress (mcoins δF chals) (BalanceQ.liftRec (L := 𝕂′) r) ≠ 0 := by
  obtain ⟨hs, -⟩ := walkChipJ8_to_HQK δF kroots b hn nodes orbit chals pubs Q hsat hbind hF hp
  rw [← walkXReqs_bitFix]
  exact walkHQK_reqs_denQ δF kroots b hn nodes orbit chals pubs _ hs

end J8

end Walk

end

end Nock.NockVMROM.Thm54.VclL.Handle.WalkTeleJ8
