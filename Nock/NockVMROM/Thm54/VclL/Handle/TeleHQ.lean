/-
  Nock/NockVMROM/Thm54/VclL/Handle/TeleHQ.lean

  Additive.

  * `qTelescope` — the generic init / step / terminal telescope with `𝕂′` accumulators and base masks;
  * `denKeyQ_ev` — a `𝕂′` key denominator is `compress` at the `𝕂′` coins `(γH′, ρH′)` of the lifted
    key (`liftRec ∘ keyVec5`);
  * cell twin: `cellHQ_inv` (`invH′ · den′ = 1`), `cellHQ_telescope` (`Σ mh · invH′ = (pub₄, pub₅)`);
  * walk twin: `walkHQ_inv` (three inverses), `walkHQ_telescopeX` (`Σ invX′ = (pub₄, pub₅)`),
    `walkHQ_telescopeP` (`Σ mL · invL′ + mR · invR′ = (pub₆, pub₇)`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CellTraceHQ
import Nock.NockVMROM.Thm54.VclL.Handle.WalkTraceHQ
import Nock.NockVMROM.Thm54.VclL.Handle.TeleH
import Nock.NockVMROM.Thm54.VclL.Handle.ServeH
import Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Generic pieces -/

section Generic
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- **The `𝕂′` telescope** with base-field masks. -/
theorem qTelescope {n : ℕ} (hn : 0 < n) (fF fL : Fin n → F) (acc term : Fin n → 𝕂′) (pub : 𝕂′)
    (hF : ∀ i, fF i = if (i : ℕ) = 0 then 1 else 0)
    (hL : ∀ i, fL i = if (i : ℕ) = n - 1 then 1 else 0)
    (h0 : ∀ i, liftQ δF (fF i) * (acc i - term i) = 0)
    (hs : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
      liftQ δF (1 - fL i) * (acc ⟨(i : ℕ) + 1, hi⟩ - acc i - term ⟨(i : ℕ) + 1, hi⟩) = 0)
    (hT : ∀ i, liftQ δF (fL i) * (acc i - pub) = 0) :
    ∑ i, term i = pub := by
  set A : ℕ → 𝕂′ := fun k => if hk : k < n then acc ⟨k, hk⟩ else 0 with hA
  set T : ℕ → 𝕂′ := fun k => if hk : k < n then term ⟨k, hk⟩ else 0 with hTm
  have e0 : A 0 = T 0 := by
    simp only [hA, hTm, dif_pos hn]
    have g := h0 ⟨0, hn⟩
    rw [hF, if_pos rfl] at g
    simpa [liftQ, sub_eq_zero] using g
  have es : ∀ i, i + 1 < n → A (i + 1) = A i + T (i + 1) := by
    intro i hi
    simp only [hA, hTm, dif_pos hi, dif_pos (show i < n by omega)]
    have g := hs ⟨i, by omega⟩ hi
    rw [hL, if_neg (by simp; omega)] at g
    simp only [sub_zero, liftQ, map_one, one_mul] at g
    linear_combination g
  have eT : A (n - 1) = pub := by
    simp only [hA, dif_pos (show n - 1 < n by omega)]
    have g := hT ⟨n - 1, by omega⟩
    rw [hL, if_pos rfl] at g
    simpa [liftQ, sub_eq_zero] using g
  have := Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.telescope n hn A T pub e0 es eT
  rw [Finset.sum_range] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hTm, dif_pos i.isLt]

theorem gpowQ_ev (eK : Env K) (eF : Env F) :
    ∀ m, (HQ.gpowQ δF m).ev δF eK eF = (Quad.mk _ (eK.chal 33) (eK.chal 35)) ^ m
  | 0 => by simp [HQ.gpowQ, ev_one]
  | m + 1 => by rw [HQ.gpowQ, ev_mul, HQ.gamQ, ev_chal, gpowQ_ev eK eF m]; ring

theorem rlcQ_ev (eK : Env K) (eF : Env F) :
    ∀ (l : List (CoeffExpr F)) (m : ℕ), (HQ.rlcQ δF m l).ev δF eK eF =
      ∑ c ∈ Finset.range l.length, (Quad.mk _ (eK.chal 33) (eK.chal 35)) ^ (m + c) *
        liftQ δF ((l.getD c (.const 0)).eval eF)
  | [], m => by simp [HQ.rlcQ, ev_zero]
  | g :: r, m => by
    rw [HQ.rlcQ, ev_add, ev_mul, ev_base, gpowQ_ev, rlcQ_ev eK eF r (m + 1), List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show m + 1 + c = m + (c + 1) by omega]

/-- The `𝕂′` coins as read at the memory challenge leaves `33 / 35`, `34 / 36`. -/
def coinsQ (eK : Env K) : IOCoins 𝕂′ := ⟨Quad.mk _ (eK.chal 33) (eK.chal 35), Quad.mk _ (eK.chal 34) (eK.chal 36)⟩

/-- **A `𝕂′` key denominator is `compress` of the lifted key at the `𝕂′` coins.** -/
theorem denKeyQ_ev (eK : Env K) (eF : Env F) (l : List (CoeffExpr F)) (hl : l.length = 5) :
    (HQ.denKeyQ δF l).ev δF eK eF = compress (coinsQ δF eK) (liftRec (K := K) (L := 𝕂′) (ServeH.keyVec5 l eF)) := by
  simp only [HQ.denKeyQ, ev_add, HQ.rhoQ, ev_chal, rlcQ_ev, hl, compress, Walk.rlc, coinsQ, zero_add]
  congr 1

end Generic

/-! ## 2. The `𝕂′` cell twin -/

section Cell
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (cellChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X])

local notation "𝕂′" => Quad (algebraMap F K δF)

abbrev qcEF {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : Env F :=
  Reify.envOfTrace Q' orbit.ω (nodes i) (slotVal b 130 chals) (slotVal b 130 pubs)

abbrev qcEK {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : Env K :=
  gatherEnv b ((cellTemplateHQ δF).col0 3) (qcEF b nodes orbit chals pubs Q' i)

theorem cellHQ_qgates (hsat : (cellChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    ∀ e ∈ CellHQ.gatesQ δF, e.ev δF (qcEK δF b nodes orbit chals pubs Q i) (qcEF b nodes orbit chals pubs Q i) = 0 := by
  have hl := (expandChip_satisfies_iff_language (cellTemplateHQ δF) b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)
  intro e he
  exact ev_eq_zero_of_gates δF _ _ e fun g hg =>
    hl.2.2.2 g (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hg⟩))

/-- The `𝕂′` provide inverse of row `i`. -/
abbrev cInvQ {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : 𝕂′ :=
  Quad.mk _ ((qcEK δF b nodes orbit chals pubs Q' i).trace CellHQ.invHQ)
    ((qcEK δF b nodes orbit chals pubs Q' i).trace (CellHQ.invHQ + 1))

abbrev cDenQ {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : 𝕂′ :=
  (HQ.denKeyQ δF (CellH.keyH (F := F))).ev δF (qcEK δF b nodes orbit chals pubs Q' i) (qcEF b nodes orbit chals pubs Q' i)

abbrev cTermQ {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : 𝕂′ :=
  liftQ δF ((qcEF b nodes orbit chals pubs Q' i).trace CellH.mh) * cInvQ δF b nodes orbit chals pubs Q' i

/-- **The `𝕂′` provide inverse**: `invH′ · den′ = 1`. -/
theorem cellHQ_inv (hsat : (cellChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    cDenQ δF b nodes orbit chals pubs Q i ≠ 0 ∧
      cInvQ δF b nodes orbit chals pubs Q i = (cDenQ δF b nodes orbit chals pubs Q i)⁻¹ := by
  have g := cellHQ_qgates δF b hn nodes orbit chals pubs Q hsat i
    (QE.sub (QE.mul δF (QE.var CellHQ.invHQ) (HQ.denKeyQ δF CellH.keyH)) QE.one) (by simp [CellHQ.gatesQ])
  rw [ev_sub, ev_mul, ev_var, ev_one, sub_eq_zero] at g
  exact ⟨right_ne_zero_of_mul_eq_one g, eq_inv_of_mul_eq_one_left g⟩

theorem cellHQ_masks (hbind : (cellChipHQ δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (qcEF b nodes orbit chals pubs Q i).trace Cell.isF = (if (i : ℕ) = 0 then 1 else 0) ∧
      (qcEF b nodes orbit chals pubs Q i).trace Cell.isL = (if (i : ℕ) = n - 1 then 1 else 0) := by
  have hw : (cellChipHQ δF b hn nodes orbit chals pubs).rap.w = 238 := cellChipHQ_width δF b hn nodes orbit chals pubs
  have h0 : Q ⟨0, by rw [hw]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 2; omega⟩
  have h1 : Q ⟨1, by rw [hw]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 2; omega⟩
  exact masks_of hn nodes orbit Q _ _ h0 h1 hinj _ _ i

theorem qcEK_pub (i : Fin n) (idx : ℕ) : (qcEK δF b nodes orbit chals pubs Q i).pub idx = pubs idx :=
  gather_pub_T b (cellTemplateHQ δF) 130 (cellTemplateHQ_baseCols δF) _ pubs rfl idx

theorem qcEK_chal (i : Fin n) (idx : ℕ) : (qcEK δF b nodes orbit chals pubs Q i).chal idx = chals idx :=
  gather_chal_T b (cellTemplateHQ δF) 130 (cellTemplateHQ_baseCols δF) _ chals rfl idx

theorem qcEF_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (j : ℕ) :
    (qcEF b nodes orbit chals pubs Q i).traceNext j = (qcEF b nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩).trace j :=
  traceNext_eq nodes orbit Q _ _ hadj i hi j

theorem qcEK_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (r : ℕ) :
    (qcEK δF b nodes orbit chals pubs Q i).traceNext r = (qcEK δF b nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩).trace r :=
  gather_next_T b _ _ _ (qcEF_next δF b hn nodes orbit chals pubs Q hadj i hi) r

/-- **The `𝕂′` cell export telescope**: `Σ_i mhᵢ · invH′ᵢ = (pub₄, pub₅)`. -/
theorem cellHQ_telescope (hsat : (cellChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChipHQ δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ i, cTermQ δF b nodes orbit chals pubs Q i = Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) := by
  have hg := cellHQ_qgates δF b hn nodes orbit chals pubs Q hsat
  refine qTelescope δF hn (fun i => (qcEF b nodes orbit chals pubs Q i).trace Cell.isF)
    (fun i => (qcEF b nodes orbit chals pubs Q i).trace Cell.isL)
    (fun i => Quad.mk _ ((qcEK δF b nodes orbit chals pubs Q i).trace CellHQ.accHQ)
      ((qcEK δF b nodes orbit chals pubs Q i).trace (CellHQ.accHQ + 1))) _ _
    (fun i => (cellHQ_masks δF b hn nodes orbit chals pubs Q hbind hinj i).1)
    (fun i => (cellHQ_masks δF b hn nodes orbit chals pubs Q hbind hinj i).2) ?_ ?_ ?_
  · intro i
    have g := hg i _ (by simp [CellHQ.gatesQ] : QE.scale (cv Cell.isF) (QE.sub (QE.var CellHQ.accHQ)
      (QE.scale (cv CellH.mh) (QE.var CellHQ.invHQ))) ∈ CellHQ.gatesQ δF)
    rw [ev_scale, ev_sub, ev_var, ev_scale, ev_var] at g
    simpa only [cv, CoeffExpr.eval] using g
  · intro i hi
    have g := hg i _ (by simp [CellHQ.gatesQ] : QE.scale (notE (cv Cell.isL)) (QE.sub (QE.sub (QE.next CellHQ.accHQ)
      (QE.var CellHQ.accHQ)) (QE.scale (nv CellH.mh) (QE.next CellHQ.invHQ))) ∈ CellHQ.gatesQ δF)
    rw [ev_scale, ev_sub, ev_sub, ev_next, ev_var, ev_scale, ev_next] at g
    simp only [notE, cv, nv, CoeffExpr.eval, qcEK_next δF b hn nodes orbit chals pubs Q hadj i hi,
      qcEF_next δF b hn nodes orbit chals pubs Q hadj i hi] at g
    simpa only [cTermQ, cInvQ, liftQ, map_sub, map_one] using g
  · intro i
    have g := hg i _ (by simp [CellHQ.gatesQ] : QE.scale (cv Cell.isL) (QE.sub (QE.var CellHQ.accHQ)
      (QE.pub CellHQ.pubHQ)) ∈ CellHQ.gatesQ δF)
    rw [ev_scale, ev_sub, ev_var, ev_pub, qcEK_pub, qcEK_pub] at g
    simpa only [cv, CoeffExpr.eval] using g

/-- The cell twin's row denominator is `compress` at the `𝕂′` coins of the lifted key. -/
theorem cDenQ_eq (i : Fin n) :
    cDenQ δF b nodes orbit chals pubs Q i =
      compress ⟨Quad.mk _ (chals 33) (chals 35), Quad.mk _ (chals 34) (chals 36)⟩
        (liftRec (K := K) (L := 𝕂′) (ServeH.keyVec5 (CellH.keyH (F := F)) (qcEF b nodes orbit chals pubs Q i))) := by
  rw [cDenQ, denKeyQ_ev δF _ _ _ (by simp [CellH.keyH])]
  simp only [coinsQ, qcEK_chal]

end Cell

/-! ## 3. The `𝕂′` walk twin -/

section Walk
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kroots : ℕ)
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.w → F[X])

local notation "𝕂′" => Quad (algebraMap F K δF)

abbrev qwEF {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : Env F :=
  Reify.envOfTrace Q' orbit.ω (nodes i) (slotVal b 25 chals) (slotVal b 25 pubs)

abbrev qwEK {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : Env K :=
  gatherEnv b ((walkTemplateHQ δF kroots).col0 3) (qwEF b nodes orbit chals pubs Q' i)

theorem walkHQ_qgates (hsat : (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    ∀ e ∈ WalkHQ.gatesQ δF,
      e.ev δF (qwEK δF kroots b nodes orbit chals pubs Q i) (qwEF b nodes orbit chals pubs Q i) = 0 := by
  have hl := (expandChip_satisfies_iff_language (walkTemplateHQ δF kroots) b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)
  intro e he
  exact ev_eq_zero_of_gates δF _ _ e fun g hg =>
    hl.2.2.2 g (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hg⟩))

/-- The `𝕂′` value of role pair `r, r + 1` at row `i`. -/
abbrev wQ {w : ℕ} (Q' : Fin w → F[X]) (r : ℕ) (i : Fin n) : 𝕂′ :=
  Quad.mk _ ((qwEK δF kroots b nodes orbit chals pubs Q' i).trace r)
    ((qwEK δF kroots b nodes orbit chals pubs Q' i).trace (r + 1))

abbrev wDenQ {w : ℕ} (Q' : Fin w → F[X]) (l : List (CoeffExpr F)) (i : Fin n) : 𝕂′ :=
  (HQ.denKeyQ δF l).ev δF (qwEK δF kroots b nodes orbit chals pubs Q' i) (qwEF b nodes orbit chals pubs Q' i)

abbrev wPTermQ {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : 𝕂′ :=
  liftQ δF ((qwEF b nodes orbit chals pubs Q' i).trace WChip.mL) * wQ δF kroots b nodes orbit chals pubs Q' WalkHQ.hpInvLQ i +
    liftQ δF ((qwEF b nodes orbit chals pubs Q' i).trace WChip.mR) * wQ δF kroots b nodes orbit chals pubs Q' WalkHQ.hpInvRQ i

theorem inv_of_gate {x d : 𝕂′} (g : x * d - 1 = 0) : d ≠ 0 ∧ x = d⁻¹ := by
  rw [sub_eq_zero] at g
  exact ⟨right_ne_zero_of_mul_eq_one g, eq_inv_of_mul_eq_one_left g⟩

/-- **The three `𝕂′` walk inverses.** -/
theorem walkHQ_inv (hsat : (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    (wDenQ δF kroots b nodes orbit chals pubs Q WalkHC.xKeyH i ≠ 0 ∧
      wQ δF kroots b nodes orbit chals pubs Q WalkHQ.hxInvQ i = (wDenQ δF kroots b nodes orbit chals pubs Q WalkHC.xKeyH i)⁻¹) ∧
    (wDenQ δF kroots b nodes orbit chals pubs Q WalkHC.recLH i ≠ 0 ∧
      wQ δF kroots b nodes orbit chals pubs Q WalkHQ.hpInvLQ i = (wDenQ δF kroots b nodes orbit chals pubs Q WalkHC.recLH i)⁻¹) ∧
    (wDenQ δF kroots b nodes orbit chals pubs Q WalkHC.recRH i ≠ 0 ∧
      wQ δF kroots b nodes orbit chals pubs Q WalkHQ.hpInvRQ i = (wDenQ δF kroots b nodes orbit chals pubs Q WalkHC.recRH i)⁻¹) := by
  have hg := walkHQ_qgates δF kroots b hn nodes orbit chals pubs Q hsat i
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

theorem walkHQ_masks (hbind : (walkChipHQ δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (qwEF b nodes orbit chals pubs Q i).trace WChip.isF = (if (i : ℕ) = 0 then 1 else 0) ∧
      (qwEF b nodes orbit chals pubs Q i).trace WChip.isL = (if (i : ℕ) = n - 1 then 1 else 0) := by
  have hw : (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.w = 166 :=
    walkChipHQ_width δF kroots b hn nodes orbit chals pubs
  have h0 : Q ⟨0, by rw [hw]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 3; omega⟩
  have h1 : Q ⟨1, by rw [hw]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 3; omega⟩
  exact masks_of hn nodes orbit Q _ _ h0 h1 hinj _ _ i

theorem qwEK_pub (i : Fin n) (idx : ℕ) : (qwEK δF kroots b nodes orbit chals pubs Q i).pub idx = pubs idx :=
  gather_pub_T b (walkTemplateHQ δF kroots) 25 (walkTemplateHQ_baseCols δF kroots) _ pubs rfl idx

theorem qwEK_chal (i : Fin n) (idx : ℕ) : (qwEK δF kroots b nodes orbit chals pubs Q i).chal idx = chals idx :=
  gather_chal_T b (walkTemplateHQ δF kroots) 25 (walkTemplateHQ_baseCols δF kroots) _ chals rfl idx

theorem qwEF_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (j : ℕ) :
    (qwEF b nodes orbit chals pubs Q i).traceNext j = (qwEF b nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩).trace j :=
  traceNext_eq nodes orbit Q _ _ hadj i hi j

theorem qwEK_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (r : ℕ) :
    (qwEK δF kroots b nodes orbit chals pubs Q i).traceNext r =
      (qwEK δF kroots b nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩).trace r :=
  gather_next_T b _ _ _ (qwEF_next δF kroots b hn nodes orbit chals pubs Q hadj i hi) r

/-- **The `𝕂′` walk export telescope**: `Σ_i invX′ᵢ = (pub₄, pub₅)`. -/
theorem walkHQ_telescopeX (hsat : (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipHQ δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ i, wQ δF kroots b nodes orbit chals pubs Q WalkHQ.hxInvQ i =
      Quad.mk _ (pubs WalkHQ.pubXQ) (pubs (WalkHQ.pubXQ + 1)) := by
  have hg := walkHQ_qgates δF kroots b hn nodes orbit chals pubs Q hsat
  refine qTelescope δF hn (fun i => (qwEF b nodes orbit chals pubs Q i).trace WChip.isF)
    (fun i => (qwEF b nodes orbit chals pubs Q i).trace WChip.isL)
    (fun i => wQ δF kroots b nodes orbit chals pubs Q WalkHQ.hxAccQ i) _ _
    (fun i => (walkHQ_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj i).1)
    (fun i => (walkHQ_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj i).2) ?_ ?_ ?_
  · intro i
    have g := hg i _ (by simp [WalkHQ.gatesQ] : QE.scale (cv WChip.isF) (QE.sub (QE.var WalkHQ.hxAccQ)
      (QE.var WalkHQ.hxInvQ)) ∈ WalkHQ.gatesQ δF)
    rw [ev_scale, ev_sub, ev_var, ev_var] at g
    simpa only [cv, CoeffExpr.eval] using g
  · intro i hi
    have g := hg i _ (by simp [WalkHQ.gatesQ] : QE.scale (notE (cv WChip.isL)) (QE.sub (QE.sub (QE.next WalkHQ.hxAccQ)
      (QE.var WalkHQ.hxAccQ)) (QE.next WalkHQ.hxInvQ)) ∈ WalkHQ.gatesQ δF)
    rw [ev_scale, ev_sub, ev_sub, ev_next, ev_var, ev_next] at g
    simp only [notE, cv, CoeffExpr.eval, qwEK_next δF kroots b hn nodes orbit chals pubs Q hadj i hi] at g
    simpa only [wQ, liftQ, map_sub, map_one] using g
  · intro i
    have g := hg i _ (by simp [WalkHQ.gatesQ] : QE.scale (cv WChip.isL) (QE.sub (QE.var WalkHQ.hxAccQ)
      (QE.pub WalkHQ.pubXQ)) ∈ WalkHQ.gatesQ δF)
    rw [ev_scale, ev_sub, ev_var, ev_pub, qwEK_pub, qwEK_pub] at g
    simpa only [cv, CoeffExpr.eval] using g

/-- **The `𝕂′` walk path telescope**: `Σ_i (mL · invL′ + mR · invR′) = (pub₆, pub₇)`. -/
theorem walkHQ_telescopeP (hsat : (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipHQ δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ i, wPTermQ δF kroots b nodes orbit chals pubs Q i =
      Quad.mk _ (pubs WalkHQ.pubPQ) (pubs (WalkHQ.pubPQ + 1)) := by
  have hg := walkHQ_qgates δF kroots b hn nodes orbit chals pubs Q hsat
  refine qTelescope δF hn (fun i => (qwEF b nodes orbit chals pubs Q i).trace WChip.isF)
    (fun i => (qwEF b nodes orbit chals pubs Q i).trace WChip.isL)
    (fun i => wQ δF kroots b nodes orbit chals pubs Q WalkHQ.hpAccQ i) _ _
    (fun i => (walkHQ_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj i).1)
    (fun i => (walkHQ_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj i).2) ?_ ?_ ?_
  · intro i
    have g := hg i _ (by simp [WalkHQ.gatesQ] : QE.scale (cv WChip.isF) (QE.sub (QE.var WalkHQ.hpAccQ)
      (WalkHQ.pTermQ true)) ∈ WalkHQ.gatesQ δF)
    simp only [WalkHQ.pTermQ, if_true, ev_scale, ev_sub, ev_add, ev_var] at g
    simpa only [cv, CoeffExpr.eval] using g
  · intro i hi
    have g := hg i _ (by simp [WalkHQ.gatesQ] : QE.scale (notE (cv WChip.isL)) (QE.sub (QE.sub (QE.next WalkHQ.hpAccQ)
      (QE.var WalkHQ.hpAccQ)) (WalkHQ.pTermQ false)) ∈ WalkHQ.gatesQ δF)
    simp only [WalkHQ.pTermQ, Bool.false_eq_true, if_false, ev_scale, ev_sub, ev_add, ev_var, ev_next] at g
    simp only [notE, cv, nv, CoeffExpr.eval, qwEK_next δF kroots b hn nodes orbit chals pubs Q hadj i hi,
      qwEF_next δF kroots b hn nodes orbit chals pubs Q hadj i hi] at g
    simpa only [wPTermQ, wQ, liftQ, map_sub, map_one] using g
  · intro i
    have g := hg i _ (by simp [WalkHQ.gatesQ] : QE.scale (cv WChip.isL) (QE.sub (QE.var WalkHQ.hpAccQ)
      (QE.pub WalkHQ.pubPQ)) ∈ WalkHQ.gatesQ δF)
    rw [ev_scale, ev_sub, ev_var, ev_pub, qwEK_pub, qwEK_pub] at g
    simpa only [cv, CoeffExpr.eval] using g

theorem wDenQ_eq (l : List (CoeffExpr F)) (hl : l.length = 5) (i : Fin n) :
    wDenQ δF kroots b nodes orbit chals pubs Q l i =
      compress ⟨Quad.mk _ (chals 33) (chals 35), Quad.mk _ (chals 34) (chals 36)⟩
        (liftRec (K := K) (L := 𝕂′) (ServeH.keyVec5 l (qwEF b nodes orbit chals pubs Q i))) := by
  rw [wDenQ, denKeyQ_ev δF _ _ _ hl]
  simp only [coinsQ, qwEK_chal]

end Walk

end

end Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ
