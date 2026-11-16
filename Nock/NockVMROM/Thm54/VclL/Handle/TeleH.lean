/-
  Nock/NockVMROM/Thm54/VclL/Handle/TeleH.lean

  Additive.

  * §1 a generic `𝕂` telescope `kTelescope` (init / step / terminal gates under the first/last
    masks give `Σ term = pub`), and the generic gathered-leaf lemmas `gather_chal_T` / `gather_pub_T`
    / `gather_next_T` for any template at base width `B` (`sum_slotVal`).
  * §2 the cell twin `cellChipH`: row gates (`cellH_rows`), masks (`cellH_masks`), the handle-export
    provide inverse (`cellH_inv`: `invH · den = 1`, so `den ≠ 0` and `invH = den⁻¹`) and
    **`cellH_export_telescope`**: `Σ_i mhᵢ · invHᵢ = pubs 4`.
  * §3 the walk twin `walkChipH`: row gates, masks, the three inverses, and
    **`walkH_export_telescope`** (`Σ_j hxInvⱼ = pubs 4`) and **`walkH_path_telescope`**
    (`Σ_j (mLⱼ·invLⱼ + mRⱼ·invRⱼ) = pubs 5`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkH
import Nock.NockVMROM.Thm54.VclL.Chips.Telescope

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Handle.TeleH

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Generic pieces -/

section Generic
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **The `𝕂` telescope**: init `isF·(acc − term) = 0`, step `(1 − isL)·(acc' − acc − term') = 0`,
terminal `isL·(acc − pub) = 0` under the endpoint masks give `Σ term = pub`. -/
theorem kTelescope {n : ℕ} (hn : 0 < n) (fF fL : Fin n → F) (acc term : Fin n → K) (pub : K)
    (hF : ∀ i, fF i = if (i : ℕ) = 0 then 1 else 0)
    (hL : ∀ i, fL i = if (i : ℕ) = n - 1 then 1 else 0)
    (h0 : ∀ i, algebraMap F K (fF i) * (acc i - term i) = 0)
    (hs : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
      algebraMap F K (1 - fL i) * (acc ⟨(i : ℕ) + 1, hi⟩ - acc i - term ⟨(i : ℕ) + 1, hi⟩) = 0)
    (hT : ∀ i, algebraMap F K (fL i) * (acc i - pub) = 0) :
    ∑ i, term i = pub := by
  set A : ℕ → K := fun k => if hk : k < n then acc ⟨k, hk⟩ else 0 with hA
  set T : ℕ → K := fun k => if hk : k < n then term ⟨k, hk⟩ else 0 with hTm
  have e0 : A 0 = T 0 := by
    simp only [hA, hTm, dif_pos hn]
    have g := h0 ⟨0, hn⟩
    rw [hF, if_pos rfl, map_one, one_mul] at g
    exact sub_eq_zero.mp g
  have es : ∀ i, i + 1 < n → A (i + 1) = A i + T (i + 1) := by
    intro i hi
    simp only [hA, hTm, dif_pos hi, dif_pos (show i < n by omega)]
    have g := hs ⟨i, by omega⟩ hi
    rw [hL, if_neg (by simp; omega), sub_zero, map_one, one_mul] at g
    linear_combination g
  have eT : A (n - 1) = pub := by
    simp only [hA, dif_pos (show n - 1 < n by omega)]
    have g := hT ⟨n - 1, by omega⟩
    rw [hL, if_pos rfl, map_one, one_mul] at g
    exact sub_eq_zero.mp g
  have := Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.telescope n hn A T pub e0 es eT
  rw [Finset.sum_range] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hTm, dif_pos i.isLt]

variable (b : Basis (Fin 3) F K)

theorem gather_chal_T (T : ChipTemplate F) (B : ℕ) (hB : T.baseCols = B) (env : Env F) (chals : ℕ → K)
    (henv : env.chal = slotVal b B chals) (idx : ℕ) : (gatherEnv b (T.col0 3) env).chal idx = chals idx := by
  simp only [gatherEnv, ChipTemplate.col0, hB, henv]
  exact sum_slotVal b B idx chals

theorem gather_pub_T (T : ChipTemplate F) (B : ℕ) (hB : T.baseCols = B) (env : Env F) (pubs : ℕ → K)
    (henv : env.pub = slotVal b B pubs) (idx : ℕ) : (gatherEnv b (T.col0 3) env).pub idx = pubs idx := by
  simp only [gatherEnv, ChipTemplate.col0, hB, henv]
  exact sum_slotVal b B idx pubs

/-- The gathered next-row `𝕂` value is the next row's gathered value. -/
theorem gather_next_T (T : ChipTemplate F) (env env' : Env F) (h : ∀ j, env.traceNext j = env'.trace j)
    (r : ℕ) : (gatherEnv b (T.col0 3) env).traceNext r = (gatherEnv b (T.col0 3) env').trace r := by
  simp only [gatherEnv, ChipTemplate.col0, h]

/-- Endpoint masks of a twin from its preprocessing binding. -/
theorem masks_of {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) {w : ℕ}
    (Q : Fin w → F[X]) (hw0 : 0 < w) (hw1 : 1 < w) (h0 : Q ⟨0, hw0⟩ = firstRowMask nodes)
    (h1 : Q ⟨1, hw1⟩ = lastRowMask hn nodes) (hinj : Function.Injective nodes) (cv pv : ℕ → F)
    (i : Fin n) :
    (Reify.envOfTrace Q orbit.ω (nodes i) cv pv).trace 0 = (if (i : ℕ) = 0 then 1 else 0) ∧
      (Reify.envOfTrace Q orbit.ω (nodes i) cv pv).trace 1 = (if (i : ℕ) = n - 1 then 1 else 0) := by
  rw [envOfTrace_trace Q _ _ _ _ hw0, envOfTrace_trace Q _ _ _ _ hw1, h0, h1,
    firstRowMask_eval nodes hinj i, lastRowMask_eval hn nodes hinj i]
  refine ⟨rfl, ?_⟩
  by_cases hi : (i : ℕ) = n - 1
  · rw [if_pos (Fin.ext hi), if_pos hi]
  · rw [if_neg (fun h => hi (congrArg Fin.val h)), if_neg hi]

end Generic

/-! ## 2. The cell twin -/

section Cell
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (cellChipH δF b hn nodes orbit chals pubs).rap.w → F[X])

/-- Row `i`'s base environment on the cell twin. -/
abbrev cEF {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : Env F :=
  Reify.envOfTrace Q' orbit.ω (nodes i) (slotVal b 130 chals) (slotVal b 130 pubs)

/-- Row `i`'s gathered `𝕂` environment on the cell twin. -/
abbrev cEK {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : Env K :=
  gatherEnv b ((cellTemplateH δF).col0 3) (cEF b nodes orbit chals pubs Q' i)

theorem cellH_rows (hsat : (cellChipH δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    (∀ g ∈ Cell.baseGates (F := F), g.eval (cEF b nodes orbit chals pubs Q i) = 0) ∧
      ∀ g ∈ Cell.mixedGates δF ++ CellH.gates,
        g.eval (cEK δF b nodes orbit chals pubs Q i) (cEF b nodes orbit chals pubs Q i) = 0 := by
  have hl := (expandChip_satisfies_iff_language (cellTemplateH δF) b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)
  exact ⟨hl.1, hl.2.2.2⟩

theorem cellH_hgate (hsat : (cellChipH δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n)
    (g : MixedExpr F) (hg : g ∈ CellH.gates) :
    g.eval (cEK δF b nodes orbit chals pubs Q i) (cEF b nodes orbit chals pubs Q i) = 0 :=
  (cellH_rows δF b hn nodes orbit chals pubs Q hsat i).2 g (List.mem_append_right _ hg)

theorem cellH_w : (cellChipH δF b hn nodes orbit chals pubs).rap.w = 232 :=
  cellChipH_width δF b hn nodes orbit chals pubs

theorem cellH_masks (hbind : (cellChipH δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (cEF b nodes orbit chals pubs Q i).trace Cell.isF = (if (i : ℕ) = 0 then 1 else 0) ∧
      (cEF b nodes orbit chals pubs Q i).trace Cell.isL = (if (i : ℕ) = n - 1 then 1 else 0) := by
  have h0 : Q ⟨0, by rw [cellH_w]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 2; omega⟩
  have h1 : Q ⟨1, by rw [cellH_w]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 2; omega⟩
  exact masks_of hn nodes orbit Q _ _ h0 h1 hinj _ _ i

theorem cEK_chal (i : Fin n) (idx : ℕ) : (cEK δF b nodes orbit chals pubs Q i).chal idx = chals idx :=
  gather_chal_T b (cellTemplateH δF) 130 (cellTemplateH_baseCols δF) _ chals rfl idx

theorem cEK_pub (i : Fin n) (idx : ℕ) : (cEK δF b nodes orbit chals pubs Q i).pub idx = pubs idx :=
  gather_pub_T b (cellTemplateH δF) 130 (cellTemplateH_baseCols δF) _ pubs rfl idx

theorem cEF_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (j : ℕ) :
    (cEF b nodes orbit chals pubs Q i).traceNext j = (cEF b nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩).trace j :=
  traceNext_eq nodes orbit Q _ _ hadj i hi j

theorem cEK_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (r : ℕ) :
    (cEK δF b nodes orbit chals pubs Q i).traceNext r = (cEK δF b nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩).trace r :=
  gather_next_T b _ _ _ (cEF_next δF b hn nodes orbit chals pubs Q hadj i hi) r

/-- The handle-export provide term of row `i`: `mh · invH`. -/
abbrev cTermH {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : K :=
  algebraMap F K ((cEF b nodes orbit chals pubs Q' i).trace CellH.mh) * (cEK δF b nodes orbit chals pubs Q' i).trace CellH.invH

/-- The handle-export denominator of row `i` (`ρH + RLC^{γH}(keyH)`). -/
abbrev cDenH {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : K :=
  (CellH.denKey CellH.keyH : MixedExpr F).eval (cEK δF b nodes orbit chals pubs Q' i) (cEF b nodes orbit chals pubs Q' i)

/-- **The provide inverse**: `invH · den = 1`. -/
theorem cellH_inv (hsat : (cellChipH δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    cDenH δF b nodes orbit chals pubs Q i ≠ 0 ∧
      (cEK δF b nodes orbit chals pubs Q i).trace CellH.invH = (cDenH δF b nodes orbit chals pubs Q i)⁻¹ := by
  have g := cellH_hgate δF b hn nodes orbit chals pubs Q hsat i
    (.Sub (.Mul (.Var .traceCur CellH.invH) (CellH.denKey CellH.keyH)) (.Const 1)) (by simp [CellH.gates])
  simp only [MixedExpr.eval, Int.cast_one] at g
  have hm : (cEK δF b nodes orbit chals pubs Q i).trace CellH.invH * cDenH δF b nodes orbit chals pubs Q i = 1 :=
    sub_eq_zero.mp g
  have hd : cDenH δF b nodes orbit chals pubs Q i ≠ 0 := right_ne_zero_of_mul_eq_one hm
  exact ⟨hd, eq_inv_of_mul_eq_one_left hm⟩

/-- **The cell twin's handle-export telescope**: `Σ_i mhᵢ · invHᵢ = pubs 4`. -/
theorem cellH_export_telescope (hsat : (cellChipH δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChipH δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ i, cTermH δF b nodes orbit chals pubs Q i = pubs CellH.pubH := by
  have hg := cellH_hgate δF b hn nodes orbit chals pubs Q hsat
  refine kTelescope hn (fun i => (cEF b nodes orbit chals pubs Q i).trace Cell.isF)
    (fun i => (cEF b nodes orbit chals pubs Q i).trace Cell.isL)
    (fun i => (cEK δF b nodes orbit chals pubs Q i).trace CellH.accH) _ _
    (fun i => (cellH_masks δF b hn nodes orbit chals pubs Q hbind hinj i).1)
    (fun i => (cellH_masks δF b hn nodes orbit chals pubs Q hbind hinj i).2) ?_ ?_ ?_
  · intro i
    have g := hg i (.Scale (cv Cell.isF) (.Sub (.Var .traceCur CellH.accH)
        (.Scale (cv CellH.mh) (.Var .traceCur CellH.invH)))) (by simp [CellH.gates])
    simpa only [MixedExpr.eval, CoeffExpr.eval, cv] using g
  · intro i hi
    have g := hg i (.Scale (notE (cv Cell.isL)) (.Sub (.Sub (.Var .traceNext CellH.accH) (.Var .traceCur CellH.accH))
        (.Scale (nv CellH.mh) (.Var .traceNext CellH.invH)))) (by simp [CellH.gates])
    simp only [MixedExpr.eval, CoeffExpr.eval, cv, nv, notE,
      cEK_next δF b hn nodes orbit chals pubs Q hadj i hi,
      cEF_next δF b hn nodes orbit chals pubs Q hadj i hi] at g
    simpa only [cTermH] using g
  · intro i
    have g := hg i (.Scale (cv Cell.isL) (.Sub (.Var .traceCur CellH.accH) (.Var .publicVal CellH.pubH)))
      (by simp [CellH.gates])
    simp only [MixedExpr.eval, CoeffExpr.eval, cv, cEK_pub] at g
    exact g

end Cell

/-! ## 3. The walk twin -/

section Walk
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kroots : ℕ)
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChipH δF kroots b hn nodes orbit chals pubs).rap.w → F[X])

abbrev wEF {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : Env F :=
  Reify.envOfTrace Q' orbit.ω (nodes i) (slotVal b 25 chals) (slotVal b 25 pubs)

abbrev wEK {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : Env K :=
  gatherEnv b ((walkTemplateH δF kroots).col0 3) (wEF b nodes orbit chals pubs Q' i)

theorem walkH_hgate (hsat : (walkChipH δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n)
    (g : MixedExpr F) (hg : g ∈ WalkHC.gates) :
    g.eval (wEK δF kroots b nodes orbit chals pubs Q i) (wEF b nodes orbit chals pubs Q i) = 0 := by
  have hl := (expandChip_satisfies_iff_language (walkTemplateH δF kroots) b _ _ orbit _ Q).mp hsat
    (nodes i) (mem_rowNodeSet nodes i)
  exact hl.2.2.2 g (List.mem_append_right _ hg)

theorem walkH_base (hsat : (walkChipH δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n)
    (g : CoeffExpr F) (hg : g ∈ WChip.baseGates kroots ++ WalkHC.baseH) :
    g.eval (wEF b nodes orbit chals pubs Q i) = 0 :=
  ((expandChip_satisfies_iff_language (walkTemplateH δF kroots) b _ _ orbit _ Q).mp hsat
    (nodes i) (mem_rowNodeSet nodes i)).1 g hg

theorem walkH_w : (walkChipH δF kroots b hn nodes orbit chals pubs).rap.w = 151 :=
  walkChipH_width δF kroots b hn nodes orbit chals pubs

theorem walkH_masks (hbind : (walkChipH δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (wEF b nodes orbit chals pubs Q i).trace WChip.isF = (if (i : ℕ) = 0 then 1 else 0) ∧
      (wEF b nodes orbit chals pubs Q i).trace WChip.isL = (if (i : ℕ) = n - 1 then 1 else 0) := by
  have h0 : Q ⟨0, by rw [walkH_w]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 3; omega⟩
  have h1 : Q ⟨1, by rw [walkH_w]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 3; omega⟩
  exact masks_of hn nodes orbit Q _ _ h0 h1 hinj _ _ i

theorem wEK_pub (i : Fin n) (idx : ℕ) : (wEK δF kroots b nodes orbit chals pubs Q i).pub idx = pubs idx :=
  gather_pub_T b (walkTemplateH δF kroots) 25 (walkTemplateH_baseCols δF kroots) _ pubs rfl idx

theorem wEK_chal (i : Fin n) (idx : ℕ) : (wEK δF kroots b nodes orbit chals pubs Q i).chal idx = chals idx :=
  gather_chal_T b (walkTemplateH δF kroots) 25 (walkTemplateH_baseCols δF kroots) _ chals rfl idx

theorem wEF_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (j : ℕ) :
    (wEF b nodes orbit chals pubs Q i).traceNext j = (wEF b nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩).trace j :=
  traceNext_eq nodes orbit Q _ _ hadj i hi j

theorem wEK_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (r : ℕ) :
    (wEK δF kroots b nodes orbit chals pubs Q i).traceNext r =
      (wEK δF kroots b nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩).trace r :=
  gather_next_T b _ _ _ (wEF_next δF kroots b hn nodes orbit chals pubs Q hadj i hi) r

/-- A walk twin denominator at row `i`. -/
abbrev wDen {w : ℕ} (Q' : Fin w → F[X]) (l : List (CoeffExpr F)) (i : Fin n) : K :=
  (CellH.denKey l : MixedExpr F).eval (wEK δF kroots b nodes orbit chals pubs Q' i) (wEF b nodes orbit chals pubs Q' i)

/-- A `𝕂` role of the walk twin at row `i`. -/
abbrev wK {w : ℕ} (Q' : Fin w → F[X]) (r : ℕ) (i : Fin n) : K := (wEK δF kroots b nodes orbit chals pubs Q' i).trace r

theorem inv_facts_of {x d : K} (g : x * d - 1 = 0) : d ≠ 0 ∧ x = d⁻¹ := by
  have hm : x * d = 1 := sub_eq_zero.mp g
  exact ⟨right_ne_zero_of_mul_eq_one hm, eq_inv_of_mul_eq_one_left hm⟩

/-- **The three inverses of the walk twin**: consumed key and the two provided records. -/
theorem walkH_inv (hsat : (walkChipH δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    (wDen δF kroots b nodes orbit chals pubs Q WalkHC.xKeyH i ≠ 0 ∧
        wK δF kroots b nodes orbit chals pubs Q WalkHC.hxInv i = (wDen δF kroots b nodes orbit chals pubs Q WalkHC.xKeyH i)⁻¹) ∧
      (wDen δF kroots b nodes orbit chals pubs Q WalkHC.recLH i ≠ 0 ∧
        wK δF kroots b nodes orbit chals pubs Q WalkHC.hpInvL i = (wDen δF kroots b nodes orbit chals pubs Q WalkHC.recLH i)⁻¹) ∧
      (wDen δF kroots b nodes orbit chals pubs Q WalkHC.recRH i ≠ 0 ∧
        wK δF kroots b nodes orbit chals pubs Q WalkHC.hpInvR i = (wDen δF kroots b nodes orbit chals pubs Q WalkHC.recRH i)⁻¹) := by
  have hg := walkH_hgate δF kroots b hn nodes orbit chals pubs Q hsat i
  have g1 := hg (.Sub (.Mul (.Var .traceCur WalkHC.hxInv) (CellH.denKey WalkHC.xKeyH)) (.Const 1))
    (by simp [WalkHC.gates])
  have g2 := hg (.Sub (.Mul (.Var .traceCur WalkHC.hpInvL) (CellH.denKey WalkHC.recLH)) (.Const 1))
    (by simp [WalkHC.gates])
  have g3 := hg (.Sub (.Mul (.Var .traceCur WalkHC.hpInvR) (CellH.denKey WalkHC.recRH)) (.Const 1))
    (by simp [WalkHC.gates])
  simp only [MixedExpr.eval, Int.cast_one] at g1 g2 g3
  exact ⟨inv_facts_of g1, inv_facts_of g2, inv_facts_of g3⟩

/-- **The walk twin's handle-export consume telescope**: `Σ_j hxInvⱼ = pubs 4`. -/
theorem walkH_export_telescope (hsat : (walkChipH δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipH δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ i, wK δF kroots b nodes orbit chals pubs Q WalkHC.hxInv i = pubs WalkHC.pubX := by
  have hg := walkH_hgate δF kroots b hn nodes orbit chals pubs Q hsat
  refine kTelescope hn (fun i => (wEF b nodes orbit chals pubs Q i).trace WChip.isF)
    (fun i => (wEF b nodes orbit chals pubs Q i).trace WChip.isL)
    (fun i => wK δF kroots b nodes orbit chals pubs Q WalkHC.hxAcc i) _ _
    (fun i => (walkH_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj i).1)
    (fun i => (walkH_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj i).2) ?_ ?_ ?_
  · intro i
    have g := hg i (.Scale (cv WChip.isF) (.Sub (WalkHC.vK WalkHC.hxAcc) (WalkHC.vK WalkHC.hxInv)))
      (by simp [WalkHC.gates])
    simpa only [MixedExpr.eval, CoeffExpr.eval, cv, WalkHC.vK] using g
  · intro i hi
    have g := hg i (.Scale (notE (cv WChip.isL)) (.Sub (.Sub (WalkHC.vKn WalkHC.hxAcc) (WalkHC.vK WalkHC.hxAcc))
      (WalkHC.vKn WalkHC.hxInv))) (by simp [WalkHC.gates])
    simp only [MixedExpr.eval, CoeffExpr.eval, cv, notE, WalkHC.vK, WalkHC.vKn,
      wEK_next δF kroots b hn nodes orbit chals pubs Q hadj i hi] at g
    exact g
  · intro i
    have g := hg i (.Scale (cv WChip.isL) (.Sub (WalkHC.vK WalkHC.hxAcc) (.Var .publicVal WalkHC.pubX)))
      (by simp [WalkHC.gates])
    simp only [MixedExpr.eval, CoeffExpr.eval, cv, WalkHC.vK, wEK_pub] at g
    exact g

/-- The handle path provide term of row `i`: `mL · invL + mR · invR`. -/
abbrev wPTerm {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : K :=
  algebraMap F K ((wEF b nodes orbit chals pubs Q' i).trace WChip.mL) * wK δF kroots b nodes orbit chals pubs Q' WalkHC.hpInvL i +
    algebraMap F K ((wEF b nodes orbit chals pubs Q' i).trace WChip.mR) * wK δF kroots b nodes orbit chals pubs Q' WalkHC.hpInvR i

/-- **The walk twin's handle path provide telescope**: `Σ_j (mLⱼ·invLⱼ + mRⱼ·invRⱼ) = pubs 5`. -/
theorem walkH_path_telescope (hsat : (walkChipH δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipH δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ i, wPTerm δF kroots b nodes orbit chals pubs Q i = pubs WalkHC.pubP := by
  have hg := walkH_hgate δF kroots b hn nodes orbit chals pubs Q hsat
  refine kTelescope hn (fun i => (wEF b nodes orbit chals pubs Q i).trace WChip.isF)
    (fun i => (wEF b nodes orbit chals pubs Q i).trace WChip.isL)
    (fun i => wK δF kroots b nodes orbit chals pubs Q WalkHC.hpAcc i) _ _
    (fun i => (walkH_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj i).1)
    (fun i => (walkH_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj i).2) ?_ ?_ ?_
  · intro i
    have g := hg i (.Scale (cv WChip.isF) (.Sub (WalkHC.vK WalkHC.hpAcc) (WalkHC.pTermH true)))
      (by simp [WalkHC.gates])
    simpa only [MixedExpr.eval, CoeffExpr.eval, cv, WalkHC.vK, WalkHC.pTermH, if_true] using g
  · intro i hi
    have g := hg i (.Scale (notE (cv WChip.isL)) (.Sub (.Sub (WalkHC.vKn WalkHC.hpAcc) (WalkHC.vK WalkHC.hpAcc))
      (WalkHC.pTermH false))) (by simp [WalkHC.gates])
    simp only [MixedExpr.eval, CoeffExpr.eval, cv, nv, notE, WalkHC.vK, WalkHC.vKn, WalkHC.pTermH,
      Bool.false_eq_true, if_false,
      wEK_next δF kroots b hn nodes orbit chals pubs Q hadj i hi,
      wEF_next δF kroots b hn nodes orbit chals pubs Q hadj i hi] at g
    exact g
  · intro i
    have g := hg i (.Scale (cv WChip.isL) (.Sub (WalkHC.vK WalkHC.hpAcc) (.Var .publicVal WalkHC.pubP)))
      (by simp [WalkHC.gates])
    simp only [MixedExpr.eval, CoeffExpr.eval, cv, WalkHC.vK, wEK_pub] at g
    exact g

end Walk

end

end Nock.NockVMROM.Thm54.VclL.Handle.TeleH
