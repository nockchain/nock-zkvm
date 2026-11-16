/-
  Nock/NockVMROM/Thm54/VclL/Chips/ExportTelescopeW.lean

  Twins of `ExportTelescope.lean` §PathX / §Both /
  §PathP with the walk chip (`WalkChip.lean`) in place of the path chip: ONE export consume per row
  (key `WChip.xKey = (p, l, r, idx, 0)`, constant side slot `0`) and TWO path records per row
  (`WChip.recL = (root, l, 2·prefix, rootIdx)`, `WChip.recR = (root, r, 2·prefix + 1, rootIdx)`) with
  multiplicities `mL mR`, unconditional provider inverses.

  * §0 `walkDataOf_congr` — the walk data reads only the round-`≤ 1` columns `< 93` (no coin, no
    public); `lblRow_congr` / `keyRow_congr`.
  * §1 `walk_export_telescope` (`Σ_j xInvⱼ = y`, publics `0 / 1`), `walkXInternal` (one key per row,
    width-generic), `walk_internal_sum`.
  * §3 `walk_provider_telescope` (`Σ_j (mL·invL + mR·invR) = ρ_P`, publics `2 / 3`),
    `walkPRecords` (two per row, width-generic), `walkProviderFacts` (the path accumulator's `IOFacts`
    at `m = 8`; same record type as `pathProviderFacts`).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.WalkAcceptW
import Nock.NockVMROM.Thm54.VclL.Chips.ExportTelescope
import Nock.NockVMROM.Thm54.VclL.Chips.MemFamilyVCL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL
open Nock.ComputeTable (FP)
open Module
open scoped Polynomial

noncomputable section

/-! ## 0. The walk data reads only the round-`≤ 1` columns -/

section Congr
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h)

theorem lblRow_congr {eK eK' : Env K} {eF eF' : Env F} (hK : ∀ r < 24, eK.trace r = eK'.trace r)
    (hF : ∀ j < 21, eF.trace j = eF'.trace j) : lblRow δF eK eF = lblRow δF eK' eF' := by
  simp only [lblRow, QFP.ev_var, ev_var, WChip.cL, WChip.cR, WChip.pre, WChip.ridx, WChip.len,
    WChip.pR, WChip.rootR, hF 7 (by norm_num), hF 8 (by norm_num), hF 4 (by norm_num),
    hF 5 (by norm_num), hF 6 (by norm_num), hK 0 (by norm_num), hK 1 (by norm_num),
    hK 2 (by norm_num), hK 3 (by norm_num), hK 4 (by norm_num), hK 5 (by norm_num),
    hK 18 (by norm_num), hK 19 (by norm_num), hK 20 (by norm_num), hK 21 (by norm_num),
    hK 22 (by norm_num), hK 23 (by norm_num)]
  rfl

theorem keyRow_congr {eK eK' : Env K} {eF eF' : Env F} (hK : ∀ r < 24, eK.trace r = eK'.trace r)
    (hF : ∀ j < 21, eF.trace j = eF'.trace j) : keyRow δF eK eF = keyRow δF eK' eF' := by
  simp only [keyRow, QFP.ev_var, ev_var, WChip.idx, WChip.pR, WChip.lR, WChip.rR,
    hF 3 (by norm_num), hK 0 (by norm_num), hK 1 (by norm_num),
    hK 2 (by norm_num), hK 3 (by norm_num), hK 4 (by norm_num), hK 5 (by norm_num),
    hK 6 (by norm_num), hK 7 (by norm_num), hK 8 (by norm_num), hK 9 (by norm_num),
    hK 10 (by norm_num), hK 11 (by norm_num), hK 12 (by norm_num), hK 13 (by norm_num),
    hK 14 (by norm_num), hK 15 (by norm_num), hK 16 (by norm_num), hK 17 (by norm_num)] <;> rfl

/-- **Walk row environments read only the first `93` columns for the B0/B1 data** (B0 `< 21`, the
B1 `𝕂` roles `< 24`), whatever the coins and publics and whatever the width. -/
theorem walkEnv_congr {w w' : ℕ} (Q : Fin w → F[X]) (Q' : Fin w' → F[X]) (hw : 93 ≤ w)
    (hw' : 93 ≤ w') (hQ : ∀ (j : ℕ) (hj : j < 93), Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩)
    (chals pubs chals' pubs' : ℕ → K) (i : ℕ) :
    (∀ j < 93, (walkEnvF b hn nodes orbit chals pubs Q i).trace j =
      (walkEnvF b hn nodes orbit chals' pubs' Q' i).trace j) ∧
    (∀ r < 24, (walkEnvK δF kroots b hn nodes orbit chals pubs Q i).trace r =
      (walkEnvK δF kroots b hn nodes orbit chals' pubs' Q' i).trace r) := by
  have hF : ∀ j < 93, (walkEnvF b hn nodes orbit chals pubs Q i).trace j =
      (walkEnvF b hn nodes orbit chals' pubs' Q' i).trace j := by
    intro j hj
    unfold walkEnvF
    rw [envOfTrace_trace Q _ _ _ _ (by omega : j < w), envOfTrace_trace Q' _ _ _ _ (by omega : j < w'),
      hQ j hj]
  refine ⟨hF, ?_⟩
  unfold walkEnvK
  refine gather_trace_congr b _ (BK := 24) (fun r hr k hk => hF _ ?_)
  simp only [ChipTemplate.col0, walkTemplate_baseCols]; omega

/-- **`walkDataOf` reads only the columns `< 93`** (B0 and the B1 fingerprints): any coins, any
publics, any width. -/
theorem walkDataOf_congr {w w' : ℕ} (Q : Fin w → F[X]) (Q' : Fin w' → F[X]) (hw : 93 ≤ w)
    (hw' : 93 ≤ w') (hQ : ∀ (j : ℕ) (hj : j < 93), Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩)
    (chals pubs chals' pubs' : ℕ → K) :
    walkDataOf δF kroots b hn nodes orbit chals pubs Q =
      walkDataOf δF kroots b hn nodes orbit chals' pubs' Q' := by
  have hE := fun i => walkEnv_congr δF kroots b hn nodes orbit Q Q' hw hw' hQ chals pubs chals' pubs' i
  have hL : ∀ i, lblRow δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q i)
      (walkEnvF b hn nodes orbit chals pubs Q i) =
      lblRow δF (walkEnvK δF kroots b hn nodes orbit chals' pubs' Q' i)
        (walkEnvF b hn nodes orbit chals' pubs' Q' i) :=
    fun i => lblRow_congr δF (hE i).2 (fun j hj => (hE i).1 j (by omega))
  have hk : ∀ i, keyRow δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q i)
      (walkEnvF b hn nodes orbit chals pubs Q i) =
      keyRow δF (walkEnvK δF kroots b hn nodes orbit chals' pubs' Q' i)
        (walkEnvF b hn nodes orbit chals' pubs' Q' i) :=
    fun i => keyRow_congr δF (hE i).2 (fun j hj => (hE i).1 j (by omega))
  simp only [walkDataOf, hL, hk]

end Congr

/-! ## 1. The walk's export consume -/

section WalkX
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- A `𝕂′` column at walk row `j` (any width). -/
abbrev walkQ {w : ℕ} (Q : Fin w → F[X]) (r j : ℕ) : Quad (algebraMap F K δF) :=
  (QE.var r : QE F).ev δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q j)
    (walkEnvF b hn nodes orbit chals pubs Q j)

/-- A base column at walk row `j`. -/
abbrev walkB {w : ℕ} (Q : Fin w → F[X]) (c j : ℕ) : F := (walkEnvF b hn nodes orbit chals pubs Q j).trace c

/-- A key vector at walk row `j`. -/
abbrev walkKey {w : ℕ} (Q : Fin w → F[X]) (m : ℕ) (es : List (QE F)) (j : ℕ) :
    Fin m → Quad (algebraMap F K δF) :=
  keyVec δF m es (walkEnvK δF kroots b hn nodes orbit chals pubs Q j)
    (walkEnvF b hn nodes orbit chals pubs Q j)

/-- **The walk's consumed export keys**, one per row (width-generic). -/
def walkXInternal {w : ℕ} (Q : Fin w → F[X]) : List (Fin 11 → Quad (algebraMap F K δF)) :=
  (List.range n).map fun j => walkKey δF kroots b hn nodes orbit chals pubs Q 11 WChip.xKey j

/-- **The walk's path records**, two per row `(recL, mL)`, `(recR, mR)` (width-generic). -/
def walkPRecords {w : ℕ} (Q : Fin w → F[X]) : List ((Fin 8 → Quad (algebraMap F K δF)) × F) :=
  (List.range n).flatMap fun j =>
    [(walkKey δF kroots b hn nodes orbit chals pubs Q 8 WChip.recL j,
        walkB b hn nodes orbit chals pubs Q WChip.mL j),
     (walkKey δF kroots b hn nodes orbit chals pubs Q 8 WChip.recR j,
        walkB b hn nodes orbit chals pubs Q WChip.mR j)]

theorem walk_chal {w : ℕ} (Q : Fin w → F[X]) (j : ℕ) :
    (walkEnvK δF kroots b hn nodes orbit chals pubs Q j).chal = chals :=
  funext fun c => gather_chal_walk δF kroots b chals _ rfl c

theorem walk_pub {w : ℕ} (Q : Fin w → F[X]) (j : ℕ) :
    (walkEnvK δF kroots b hn nodes orbit chals pubs Q j).pub = pubs :=
  funext fun c => gather_pub_walk δF kroots b pubs _ rfl c

theorem walk_compressK {w : ℕ} (Q : Fin w → F[X]) (γ ρ : Quad (algebraMap F K δF))
    (hok : ChalsOK δF chals γ ρ 11) (es : List (QE F)) {m : ℕ} (hlen : es.length = m) (hm : m ≤ 11)
    (j : ℕ) :
    FiniteIO.compress (m := m) ⟨γ, ρ⟩ (walkKey δF kroots b hn nodes orbit chals pubs Q m es j) =
      (den δF es).ev δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q j)
        (walkEnvF b hn nodes orbit chals pubs Q j) := by
  rw [den_ev_compress' δF es hlen _ _ γ ρ]
  rw [walk_chal]; exact chalsOK_mono δF hm hok

variable (Q : Fin (walkChip δF kroots b hn nodes orbit chals pubs).rap.w → F[X])

theorem walk_w : (walkChip δF kroots b hn nodes orbit chals pubs).rap.w = 132 :=
  (walkChip_fingerprint δF kroots b hn nodes orbit chals pubs).1

theorem walk_ev_next
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : ℕ) (hi : i + 1 < n) (r : ℕ) :
    (QE.next r : QE F).ev δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q i)
        (walkEnvF b hn nodes orbit chals pubs Q i) =
      (QE.var r : QE F).ev δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q (i + 1))
        (walkEnvF b hn nodes orbit chals pubs Q (i + 1)) := by
  simp only [ev_next, ev_var, walkK_traceNext δF kroots b hn nodes orbit chals pubs Q hadj i hi]

/-- The `𝕂′` equations hold at every row. -/
theorem walk_qeqs (hsat : (walkChip δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) :
    ∀ e, e ∈ WChip.qEqs δF → ∀ j, j < n → e.ev δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q j)
      (walkEnvF b hn nodes orbit chals pubs Q j) = 0 := fun e he j hj =>
  (walk_gates δF kroots b hn nodes orbit chals pubs Q hsat j hj).2.2 e he

/-- **The walk export-consumption telescope**: `Σ_j xInvⱼ = y` (walk public slots `0 / 1`). -/
theorem walk_export_telescope (hsat : (walkChip δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChip δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ j ∈ Finset.range n, walkQ δF kroots b hn nodes orbit chals pubs Q WChip.xInv j =
      Quad.mk _ (pubs 0) (pubs 1) := by
  have hmem := walk_qeqs δF kroots b hn nodes orbit chals pubs Q hsat
  have hm := fun j hj => walk_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj j hj
  refine telescope n hn (walkQ δF kroots b hn nodes orbit chals pubs Q WChip.xAcc) _ _ ?_ ?_ ?_
  · have g := hmem (QE.scale (cv WChip.isF) (QE.sub (QE.var WChip.xAcc) (QE.var WChip.xInv)))
      (by simp [WChip.qEqs]) 0 hn
    rw [ev_scale, ev_sub] at g
    have hf : (CoeffExpr.eval (cv WChip.isF) (walkEnvF b hn nodes orbit chals pubs Q 0) : F) = 1 := by
      simp only [CoeffExpr.eval, cv]; rw [(hm 0 hn).1]; simp
    rw [hf, liftQ, map_one, map_one, one_mul] at g
    exact sub_eq_zero.mp g
  · intro i hi
    have g := hmem (QE.scale (notE (cv WChip.isL))
      (QE.sub (QE.sub (QE.next WChip.xAcc) (QE.var WChip.xAcc)) (QE.next WChip.xInv)))
      (by simp [WChip.qEqs]) i (by omega)
    rw [ev_scale, ev_sub, ev_sub, walk_ev_next δF kroots b hn nodes orbit chals pubs Q hadj i hi,
      walk_ev_next δF kroots b hn nodes orbit chals pubs Q hadj i hi] at g
    have hl : (CoeffExpr.eval (notE (cv WChip.isL)) (walkEnvF b hn nodes orbit chals pubs Q i) : F) = 1 := by
      simp only [CoeffExpr.eval, cv, notE]
      rw [(hm i (by omega)).2.1, if_neg (by omega)]; simp
    rw [hl, liftQ, map_one, map_one, one_mul] at g
    linear_combination g
  · have g := hmem (QE.scale (cv WChip.isL) (QE.sub (QE.var WChip.xAcc) (QE.pub 0)))
      (by simp [WChip.qEqs]) (n - 1) (by omega)
    rw [ev_scale, ev_sub, ev_pub] at g
    have hl : (CoeffExpr.eval (cv WChip.isL) (walkEnvF b hn nodes orbit chals pubs Q (n - 1)) : F) = 1 := by
      simp only [CoeffExpr.eval, cv]
      rw [(hm (n - 1) (by omega)).2.1, if_pos (by omega)]
    rw [hl, liftQ, map_one, map_one, one_mul, walk_pub] at g
    exact sub_eq_zero.mp g

/-- The walk export-consumer inverse: `inv·den(p, l, r, idx, 0) = 1`. -/
theorem walk_xinv (hsat : (walkChip δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) (j : ℕ)
    (hj : j < n) :
    (den δF WChip.xKey).ev δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q j)
        (walkEnvF b hn nodes orbit chals pubs Q j) ≠ 0 ∧
      walkQ δF kroots b hn nodes orbit chals pubs Q WChip.xInv j =
        ((den δF WChip.xKey).ev δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q j)
          (walkEnvF b hn nodes orbit chals pubs Q j))⁻¹ := by
  have g := walk_qeqs δF kroots b hn nodes orbit chals pubs Q hsat
    (QE.sub (QE.mul δF (QE.var WChip.xInv) (den δF WChip.xKey)) QE.one) (by simp [WChip.qEqs]) j hj
  rw [ev_sub, ev_mul, ev_one] at g
  exact prov_inv δF g

theorem walk_internal_sum (hsat : (walkChip δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChip δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11) :
    ((walkXInternal δF kroots b hn nodes orbit chals pubs Q).map fun r =>
      (FiniteIO.compress (m := 11) ⟨γ, ρ⟩ r)⁻¹).sum = Quad.mk _ (pubs 0) (pubs 1) := by
  rw [← walk_export_telescope δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj,
    walkXInternal, List.map_map, list_range_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  simp only [Function.comp_apply,
    walk_compressK δF kroots b hn nodes orbit chals pubs Q γ ρ hok WChip.xKey (m := 11) rfl le_rfl j,
    (walk_xinv δF kroots b hn nodes orbit chals pubs Q hsat j hj').2]

/-! ## 3. The path accumulator: two records per row -/

/-- The walk provider row term `mL·invL + mR·invR`. -/
abbrev pTW (j : ℕ) : Quad (algebraMap F K δF) :=
  liftQ δF (walkB b hn nodes orbit chals pubs Q WChip.mL j) *
      walkQ δF kroots b hn nodes orbit chals pubs Q WChip.pInvL j +
    liftQ δF (walkB b hn nodes orbit chals pubs Q WChip.mR j) *
      walkQ δF kroots b hn nodes orbit chals pubs Q WChip.pInvR j

/-- **The walk path-accumulator telescope**: `Σ_j (mL·invL + mR·invR) = ρ_P` (publics `2 / 3`). -/
theorem walk_provider_telescope (hsat : (walkChip δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChip δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ j ∈ Finset.range n, pTW δF kroots b hn nodes orbit chals pubs Q j = Quad.mk _ (pubs 2) (pubs 3) := by
  have hmem := walk_qeqs δF kroots b hn nodes orbit chals pubs Q hsat
  have hm := fun j hj => walk_masks δF kroots b hn nodes orbit chals pubs Q hbind hinj j hj
  refine telescope n hn (walkQ δF kroots b hn nodes orbit chals pubs Q WChip.pAcc) _ _ ?_ ?_ ?_
  · have g := hmem (QE.scale (cv WChip.isF) (QE.sub (QE.var WChip.pAcc) (WChip.pTerm true)))
      (by simp [WChip.qEqs]) 0 hn
    simp only [WChip.pTerm, if_true] at g
    rw [ev_scale, ev_sub, ev_add, ev_scale, ev_scale] at g
    have hf : (CoeffExpr.eval (cv WChip.isF) (walkEnvF b hn nodes orbit chals pubs Q 0) : F) = 1 := by
      simp only [CoeffExpr.eval, cv]; rw [(hm 0 hn).1]; simp
    rw [hf, liftQ, map_one, map_one, one_mul] at g
    exact sub_eq_zero.mp g
  · intro i hi
    have g := hmem (QE.scale (notE (cv WChip.isL))
      (QE.sub (QE.sub (QE.next WChip.pAcc) (QE.var WChip.pAcc)) (WChip.pTerm false)))
      (by simp [WChip.qEqs]) i (by omega)
    simp only [WChip.pTerm, Bool.false_eq_true, if_false] at g
    rw [ev_scale, ev_sub, ev_sub, ev_add, ev_scale, ev_scale,
      walk_ev_next δF kroots b hn nodes orbit chals pubs Q hadj i hi,
      walk_ev_next δF kroots b hn nodes orbit chals pubs Q hadj i hi,
      walk_ev_next δF kroots b hn nodes orbit chals pubs Q hadj i hi] at g
    have hl : (CoeffExpr.eval (notE (cv WChip.isL)) (walkEnvF b hn nodes orbit chals pubs Q i) : F) = 1 := by
      simp only [CoeffExpr.eval, cv, notE]
      rw [(hm i (by omega)).2.1, if_neg (by omega)]; simp
    have hmL : (CoeffExpr.eval (nv WChip.mL) (walkEnvF b hn nodes orbit chals pubs Q i) : F) =
        walkB b hn nodes orbit chals pubs Q WChip.mL (i + 1) := by
      simp only [CoeffExpr.eval, nv]; exact walk_traceNext δF kroots b hn nodes orbit chals pubs Q hadj i hi _
    have hmR : (CoeffExpr.eval (nv WChip.mR) (walkEnvF b hn nodes orbit chals pubs Q i) : F) =
        walkB b hn nodes orbit chals pubs Q WChip.mR (i + 1) := by
      simp only [CoeffExpr.eval, nv]; exact walk_traceNext δF kroots b hn nodes orbit chals pubs Q hadj i hi _
    rw [hl, hmL, hmR, liftQ, map_one, map_one, one_mul] at g
    linear_combination g
  · have g := hmem (QE.scale (cv WChip.isL) (QE.sub (QE.var WChip.pAcc) (QE.pub 2)))
      (by simp [WChip.qEqs]) (n - 1) (by omega)
    rw [ev_scale, ev_sub, ev_pub] at g
    have hl : (CoeffExpr.eval (cv WChip.isL) (walkEnvF b hn nodes orbit chals pubs Q (n - 1)) : F) = 1 := by
      simp only [CoeffExpr.eval, cv]
      rw [(hm (n - 1) (by omega)).2.1, if_pos (by omega)]
    rw [hl, liftQ, map_one, map_one, one_mul, walk_pub] at g
    exact sub_eq_zero.mp g

/-- Row `j`'s two provider inverses (unconditional). -/
theorem walk_pinv (hsat : (walkChip δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) (j : ℕ)
    (hj : j < n) :
    ((den δF WChip.recL).ev δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q j)
        (walkEnvF b hn nodes orbit chals pubs Q j) ≠ 0 ∧
      walkQ δF kroots b hn nodes orbit chals pubs Q WChip.pInvL j =
        ((den δF WChip.recL).ev δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q j)
          (walkEnvF b hn nodes orbit chals pubs Q j))⁻¹) ∧
    ((den δF WChip.recR).ev δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q j)
        (walkEnvF b hn nodes orbit chals pubs Q j) ≠ 0 ∧
      walkQ δF kroots b hn nodes orbit chals pubs Q WChip.pInvR j =
        ((den δF WChip.recR).ev δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q j)
          (walkEnvF b hn nodes orbit chals pubs Q j))⁻¹) := by
  have hmem := walk_qeqs δF kroots b hn nodes orbit chals pubs Q hsat
  have gL := hmem (QE.sub (QE.mul δF (QE.var WChip.pInvL) (den δF WChip.recL)) QE.one)
    (by simp [WChip.qEqs]) j hj
  have gR := hmem (QE.sub (QE.mul δF (QE.var WChip.pInvR) (den δF WChip.recR)) QE.one)
    (by simp [WChip.qEqs]) j hj
  rw [ev_sub, ev_mul, ev_one] at gL gR
  exact ⟨prov_inv δF gL, prov_inv δF gR⟩

/-- **The walk's path accumulator as weighted IO facts** (`m = 8`, no internal consumer):
providers = two records per row `(recL, mL)`, `(recR, mR)`, terminal `ρ_P` (publics `2 / 3`). -/
def walkProviderFacts (hsat : (walkChip δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChip δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11) :
    SVFrame.IOFacts F (FiniteIO.compress (m := 8) ⟨γ, ρ⟩) (Quad.mk _ (pubs 2) (pubs 3)) where
  records := walkPRecords δF kroots b hn nodes orbit chals pubs Q
  sum_eq := by
    rw [← walk_provider_telescope δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj,
      walkPRecords, map_flatMap_sum, list_range_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn := Finset.mem_range.mp hj
    obtain ⟨⟨-, hL⟩, ⟨-, hR⟩⟩ := walk_pinv δF kroots b hn nodes orbit chals pubs Q hsat j hjn
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      walk_compressK δF kroots b hn nodes orbit chals pubs Q γ ρ hok WChip.recL (m := 8) rfl (by norm_num) j,
      walk_compressK δF kroots b hn nodes orbit chals pubs Q γ ρ hok WChip.recR (m := 8) rfl (by norm_num) j,
      pTW, hL, hR, liftQ, IsScalarTower.algebraMap_apply F K (Quad (algebraMap F K δF))]
  ne_zero := by
    intro r hr
    obtain ⟨j, hj, hrj⟩ := List.mem_flatMap.mp hr
    have hjn := List.mem_range.mp hj
    obtain ⟨⟨hL, -⟩, ⟨hR, -⟩⟩ := walk_pinv δF kroots b hn nodes orbit chals pubs Q hsat j hjn
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hrj
    rcases hrj with rfl | rfl
    · rw [walk_compressK δF kroots b hn nodes orbit chals pubs Q γ ρ hok WChip.recL (m := 8) rfl (by norm_num) j]
      exact hL
    · rw [walk_compressK δF kroots b hn nodes orbit chals pubs Q γ ρ hok WChip.recR (m := 8) rfl (by norm_num) j]
      exact hR

end WalkX

/-! ## 2. Both tables: the export IO facts and `KeysExported` -/

section Both
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kroots : ℕ)
  (b : Basis (Fin 3) F K) {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → F)
  (orbitC : StrictOrbitDomain F 3 hC) {hP nP : ℕ} (hnP : 0 < nP) (nodesP : Fin nP → F)
  (orbitP : StrictOrbitDomain F 3 hP) (chals pubsC pubsP : ℕ → K)
  (QC : Fin (cellChip δF b hnC nodesC orbitC chals pubsC).rap.w → F[X])
  (QP : Fin (walkChip δF kroots b hnP nodesP orbitP chals pubsP).rap.w → F[X])

/-- **The export accumulator's weighted IO facts with the walk as consumer** (`cellExportFacts`
twin): providers `cellXRecords`, internal = every walk row's consumed key, terminal
`ρ_X + Σ internal`. -/
def cellExportFactsW
    (hsatC : (cellChip δF b hnC nodesC orbitC chals pubsC).rap.Satisfies QC)
    (hbindC : (cellChip δF b hnC nodesC orbitC chals pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    (hsatP : (walkChip δF kroots b hnP nodesP orbitP chals pubsP).rap.Satisfies QP)
    (hbindP : (walkChip δF kroots b hnP nodesP orbitP chals pubsP).BindsPreprocessing QP)
    (hinjP : Function.Injective nodesP)
    (hadjP : ∀ (i : Fin nP) (hi : (i : ℕ) + 1 < nP), nodesP ⟨(i : ℕ) + 1, hi⟩ = nodesP i * orbitP.ω)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11) (ρX : Quad (algebraMap F K δF))
    (hpub : Quad.mk _ (pubsC 2) (pubsC 3) = ρX + Quad.mk _ (pubsP 0) (pubsP 1)) :
    SVFrame.IOFacts F (FiniteIO.compress (m := 11) ⟨γ, ρ⟩)
      (ρX + ((walkXInternal δF kroots b hnP nodesP orbitP chals pubsP QP).map fun r =>
          (FiniteIO.compress (m := 11) ⟨γ, ρ⟩ r)⁻¹).sum) where
  records := cellXRecords δF b hnC nodesC orbitC chals pubsC QC
  sum_eq := by
    rw [cell_export_sum δF b hnC nodesC orbitC chals pubsC QC hsatC hbindC hinjC hadjC γ ρ hok, hpub,
      walk_internal_sum δF kroots b hnP nodesP orbitP chals pubsP QP hsatP hbindP hinjP hadjP γ ρ hok]
  ne_zero := by
    intro r hr
    obtain ⟨i, -, hri⟩ := List.mem_flatMap.mp hr
    obtain ⟨⟨h0, -⟩, ⟨h1, -⟩⟩ := cell_xinv_facts δF b hnC nodesC orbitC chals pubsC QC hsatC i
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hri
    rcases hri with rfl | rfl
    · rw [cell_compress (m := 11) γ ρ hok (Cell.xKeyS 0) rfl le_rfl]; exact h0
    · rw [cell_compress (m := 11) γ ρ hok (Cell.xKeyS 1) rfl le_rfl]; exact h1

/-- **Decoding a matched export key**: a walk row's consumed key equal to a cell row's side-`s`
record names that row's `(p, l, r)` and its serial. -/
theorem xKey_decodeW {w : ℕ} (QW : Fin w → F[X]) (j : ℕ) (i : Fin nC) (s : F)
    (hk : walkKey δF kroots b hnP nodesP orbitP chals pubsP QW 11 WChip.xKey j =
      cellKey δF b hnC nodesC orbitC chals pubsC QC 11 (Cell.xKeyS s) i) :
    keyRow δF (walkEnvK δF kroots b hnP nodesP orbitP chals pubsP QW j)
        (walkEnvF b hnP nodesP orbitP chals pubsP QW j) =
      ((cellRowOf δF (cellEnvK δF b nodesC orbitC chals pubsC QC i) (cellEnvF b nodesC orbitC chals pubsC QC i)).p,
       (cellRowOf δF (cellEnvK δF b nodesC orbitC chals pubsC QC i) (cellEnvF b nodesC orbitC chals pubsC QC i)).l,
       (cellRowOf δF (cellEnvK δF b nodesC orbitC chals pubsC QC i) (cellEnvF b nodesC orbitC chals pubsC QC i)).r,
       natOf (cellB δF b hnC nodesC orbitC chals pubsC QC Cell.idx i)) := by
  have e : ∀ c : Fin 11, _ := fun c => congrFun hk c
  have e0 := e ⟨0, by decide⟩; have e1 := e ⟨1, by decide⟩; have e2 := e ⟨2, by decide⟩
  have e3 := e ⟨3, by decide⟩; have e4 := e ⟨4, by decide⟩; have e5 := e ⟨5, by decide⟩
  have e6 := e ⟨6, by decide⟩; have e7 := e ⟨7, by decide⟩; have e8 := e ⟨8, by decide⟩
  have e9 := e ⟨9, by decide⟩
  simp only [walkKey, cellKey, keyVec, WChip.xKey, Cell.xKeyS, Cell.xKey, QFP.var, QFP.entries,
    List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero]
    at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  rw [ev_base, ev_base, liftQ, liftQ] at e9
  have hidx := (algebraMap F K).injective ((algebraMap K (Quad (algebraMap F K δF))).injective e9)
  simp only [CoeffExpr.eval, cv] at hidx
  simp only [keyRow, cellRowOf, cellB, QFP.ev, QFP.var, e0, e1, e2, e3, e4, e5, e6, e7, e8, hidx]

variable [Fintype K] [DecidableEq (Quad (algebraMap F K δF))] [Algebra (ZMod (ringChar F)) K]

theorem walk_keys_exported
    (hsatC : (cellChip δF b hnC nodesC orbitC chals pubsC).rap.Satisfies QC)
    (hbindC : (cellChip δF b hnC nodesC orbitC chals pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    (hsatP : (walkChip δF kroots b hnP nodesP orbitP chals pubsP).rap.Satisfies QP)
    (hbindP : (walkChip δF kroots b hnP nodesP orbitP chals pubsP).BindsPreprocessing QP)
    (hinjP : Function.Injective nodesP)
    (hadjP : ∀ (i : Fin nP) (hi : (i : ℕ) + 1 < nP), nodesP ⟨(i : ℕ) + 1, hi⟩ = nodesP i * orbitP.ω)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11) (ρX : Quad (algebraMap F K δF))
    (hpub : Quad.mk _ (pubsC 2) (pubsC 3) = ρX + Quad.mk _ (pubsP 0) (pubsP 1))
    {p : ℕ} [CharP (Quad (algebraMap F K δF)) p] (reqs : List (Fin 11 → Quad (algebraMap F K δF)))
    (hsum : (reqs.map fun r => (FiniteIO.compress (m := 11) ⟨γ, ρ⟩ r)⁻¹).sum = ρX)
    (hne : ∀ r ∈ reqs, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ r ≠ 0)
    (hγ : γ ∉ FiniteIO.IORLCCollisionEvent (FiniteIO.recordsW (reqs ++ walkXInternal δF kroots b hnP nodesP orbitP chals pubsP QP)
      (SVFrame.liftWts (cellXRecords δF b hnC nodesC orbitC chals pubsC QC))))
    (hpole : ρ ∉ FiniteIO.IOLogDerivEventW (reqs ++ walkXInternal δF kroots b hnP nodesP orbitP chals pubsP QP)
      (SVFrame.liftWts (cellXRecords δF b hnC nodesC orbitC chals pubsC QC)) γ)
    (hcount : (reqs ++ walkXInternal δF kroots b hnP nodesP orbitP chals pubsP QP).length < p) :
    WalkVCL.KeysExported (cellTableOf δF b nodesC orbitC chals pubsC QC)
      (walkDataOf δF kroots b hnP nodesP orbitP chals pubsP QP).X := by
  set M := cellExportFactsW δF kroots b hnC nodesC orbitC hnP nodesP orbitP chals pubsC pubsP QC QP
    hsatC hbindC hinjC hadjC hsatP hbindP hinjP hadjP γ ρ hok ρX hpub with hM
  have hlook := FiniteIO.finiteIO_lookup_sound_weighted (p := p)
    (reqs ++ walkXInternal δF kroots b hnP nodesP orbitP chals pubsP QP) (SVFrame.liftWts M.records) ⟨γ, ρ⟩
    (by
      intro r hr
      rcases List.mem_append.mp hr with h | h
      · exact hne r h
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
        have hj' := List.mem_range.mp hj
        rw [walk_compressK δF kroots b hnP nodesP orbitP chals pubsP QP γ ρ hok WChip.xKey (m := 11) rfl le_rfl j]
        exact (walk_xinv δF kroots b hnP nodesP orbitP chals pubsP QP hsatP j hj').1)
    (by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      exact M.ne_zero r hr)
    (by
      rw [List.map_append, List.sum_append, hsum]
      have := M.sum_eq
      simp only [SVFrame.liftWts, List.map_map, Function.comp_def]
      exact this.symm)
    hcount hγ hpole
  intro k hk
  obtain ⟨jj, rfl⟩ := List.mem_ofFn.mp hk
  have hj := jj.isLt
  have hr := hlook _ (List.mem_append_right _ (List.mem_map.mpr ⟨(jj : ℕ), List.mem_range.mpr hj, rfl⟩))
  rw [SVFrame.liftWts_fst] at hr
  obtain ⟨q, hq, hqr⟩ := List.mem_map.mp hr
  obtain ⟨i, -, hqi⟩ := List.mem_flatMap.mp hq
  have hmem : cellRowOf δF (cellEnvK δF b nodesC orbitC chals pubsC QC i) (cellEnvF b nodesC orbitC chals pubsC QC i) ∈
      cellTableOf δF b nodesC orbitC chals pubsC QC := List.mem_ofFn.mpr ⟨i, rfl⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hqi
  rcases hqi with rfl | rfl
  · rw [xKey_decodeW δF kroots b hnC nodesC orbitC hnP nodesP orbitP chals pubsC pubsP QC QP (jj : ℕ) i 0 hqr.symm]
    exact ⟨_, hmem, rfl, rfl, rfl, rfl⟩
  · rw [xKey_decodeW δF kroots b hnC nodesC orbitC hnP nodesP orbitP chals pubsC pubsP QC QP (jj : ℕ) i 1 hqr.symm]
    exact ⟨_, hmem, rfl, rfl, rfl, rfl⟩

end Both

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
