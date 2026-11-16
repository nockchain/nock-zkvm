import Nock.NockVMROM.Thm54.VclL.Compute.TowerAxHonest
import Nock.NockVMROM.Thm54.VclL.Compute.TowerRowBridge

/-!

The honest rows `rowFinal` (C1c's `genRowVals` with the tags at `childStateTagCol W (j+1)`, the walk values
of an `HonestWalk`, and the residual roles `58/59` chosen NON-CIRCULARLY as `residualVal` of the two
rows with `58/59` zeroed) and the walk-row hypotheses `WalkRowEnv` discharged at them.

`residAt` reads row `j+1` for `j+1 < n` and the extrapolation at the last row; adjacency is the package's
`AdjacentC` shape (`hadjC`, `i+1 < n` only). -/

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
open Nock.NockVMROM.Thm54.VclL.Chips Nock.Walk
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Compute.LnRead Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

section Rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **The row `j` of the honest fill with the residual roles `r58 r59` still free**: `genRowVals` at the
walk row `j` (`pub = D.pubAt j`, walk values from `D`, tags `childStateTagCol D.W (j+1)`). -/
def rowGen (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ))
    (D : HonestWalk (Quad (algebraMap F K δ))) (n : ℕ)
    (decAt : ℕ → Dec (Quad (algebraMap F K δ))) (vclAt : ℕ → ℕ → F) (j : ℕ)
    (r58 r59 : Quad (algebraMap F K δ)) : TowerRowVals (K := K) δ :=
  genRowVals (D.pubAt j) (decAt j)
    (honestEx (towerInputs (δ := δ) χ αs) (D.pubAt j) (decAt j)) j n
    (D.cnt (j + 1)) (D.acc (j + 1)) (D.ln (j + 1)) ((D.cnt (j + 1) - D.ln (j + 1))⁻¹) r58 r59
    (vclAt j) (fun k => childStateTagCol D.W (j + 1) k)

/-! ### The extrapolated next row of the last row

The orbit is NOT cyclic on the rows: `ω` has exact order `3·2^h` and `N ≤ 2^h`, so `ω·x_{N−1} ≠ x_0`
(`Batch1923.wrap_false`).  The chip's next row at row `N−1` is the evaluation of every column's interpolant at
`ω·x_{N−1}`: the Lagrange combination `lagRow (lagW nodes (ω·x_{N−1}))` of the rows. -/

/-- The Lagrange weights of the row nodes at a point `y`. -/
def lagW {n : ℕ} (nodes : Fin n → F) (y : F) (k : Fin n) : F :=
  (Lagrange.basis Finset.univ nodes k).eval y

/-- **The Lagrange combination of rows** at weights `ℓ`: base columns and the Re / Im halves of every
`𝕂′` value combined `F`-linearly; the VCL-only columns are zero (no source column reads them). -/
def lagRow {n : ℕ} (ℓ : Fin n → F) (rows : Fin n → TowerRowVals (K := K) δ) : TowerRowVals (K := K) δ where
  base c := ∑ k, ℓ k * (rows k).base c
  ext r := Quad.mk _ (∑ k, ℓ k • Quad.re _ ((rows k).ext r)) (∑ k, ℓ k • Quad.im _ ((rows k).ext r))
  walk j := Quad.mk _ (∑ k, ℓ k • Quad.re _ ((rows k).walk j)) (∑ k, ℓ k • Quad.im _ ((rows k).walk j))
  vcl _ := 0

theorem coord_sum_smul (b : Basis (Fin 3) F K) {n : ℕ} (ℓ : Fin n → F) (u : Fin n → K) (i : Fin 3) :
    CoordinateBasis.coord b (∑ k, ℓ k • u k) i = ∑ k, ℓ k * CoordinateBasis.coord b (u k) i := by
  simp [CoordinateBasis.coord, map_sum, map_smul, Finset.sum_apply]

/-- **`srcColT` is `F`-linear in the row**: the source fill of a Lagrange combination is the combination of
the fills, at every column. -/
theorem srcColT_lagRow (b : Basis (Fin 3) F K) {n : ℕ} (ℓ : Fin n → F) (rows : Fin n → TowerRowVals (K := K) δ)
    (c : ℕ) : srcColT b (lagRow ℓ rows) c = ∑ k, ℓ k * srcColT b (rows k) c := by
  unfold srcColT
  split_ifs with h1 h2 h3 h4
  · rfl
  · simp only [lagRow, Quad.re_mk]; exact coord_sum_smul b ℓ _ _
  · simp only [lagRow, Quad.re_mk]; exact coord_sum_smul b ℓ _ _
  · split
    · split_ifs with hr
      · simp only [lagRow, Quad.im_mk]; exact coord_sum_smul b ℓ _ _
      · simp only [lagRow, Quad.im_mk]; exact coord_sum_smul b ℓ _ _
    · simp
  · simp

theorem vclColT_vclCol (b : Basis (Fin 3) F K) {n : ℕ} (rows : Fin n → TowerRowVals (K := K) δ) (c : ℕ)
    (hc : SrcRead c) (k : Fin n) : vclColT b rows (vclCol c) k = srcColT b (rows k) c := by
  unfold SrcRead at hc
  rcases hc with h | h | h
  · have hv : vclCol c = c := by simp [vclCol, h]
    rw [hv]; simp [vclColT, h]
  all_goals
    have hv : vclCol c = c - 95 := by
      simp only [vclCol, serialCol]; split_ifs <;> omega
    rw [hv]
    have h1 : ¬ (c - 95 < 202) := by omega
    have h2 : (208 ≤ c - 95 ∧ c - 95 < 214) ∨ (232 ≤ c - 95 ∧ c - 95 < 394) := by omega
    simp only [vclColT, h1, h2, if_false, if_true]
    congr 1; omega

theorem vclCol_lt_src (c : ℕ) (hc : SrcRead c) : vclCol c < vclWidthT := by
  have hw : vclWidthT = 410 := rfl
  unfold SrcRead at hc
  rw [hw]; simp only [vclCol, serialCol]; split_ifs <;> omega

/-- **Next-row reads at an arbitrary point**: the pull-back's `traceNext` at `x` is the source fill of the
Lagrange combination of the rows at `ω·x` (every column's interpolant evaluated there).  No adjacency. -/
theorem pullNext_honestQT_lag (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)
    (rows : Fin n → TowerRowVals (K := K) δ) (ω x : F) (cv pv : ℕ → F) (c : ℕ) (hc : SrcRead c) :
    (pullEnv (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω x cv pv)).traceNext c =
      srcColT b (lagRow (lagW nodes (ω * x)) rows) c := by
  rw [srcColT_lagRow]
  simp only [pullEnv, Reify.envOfTrace, vclCol_lt_src c hc, dif_pos, honestQT, Lagrange.interpolate_apply,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [vclColT_vclCol b rows c hc k, lagW, mul_comm]

theorem lagRow_walk_im {n : ℕ} (ℓ : Fin n → F) (rows : Fin n → TowerRowVals (K := K) δ) (j : Fin 2)
    (h : ∀ k, Quad.im _ ((rows k).walk j) = 0) : Quad.im _ ((lagRow ℓ rows).walk j) = 0 := by
  simp [lagRow, Quad.im_mk, h]

theorem lagRow_ext_im {n : ℕ} (ℓ : Fin n → F) (rows : Fin n → TowerRowVals (K := K) δ) (r : Fin 63)
    (h : ∀ k, Quad.im _ ((rows k).ext r) = 0) : Quad.im _ ((lagRow ℓ rows).ext r) = 0 := by
  simp [lagRow, Quad.im_mk, h]

/-- The chip's next point at the last row: `ω·x_{n−1}`. -/
def lastPt {n : ℕ} (nodes : Fin n → F) (ω : F) : F :=
  if h : 0 < n then ω * nodes ⟨n - 1, by omega⟩ else 0

/-- **The extrapolated next row of the last row**: the rows `0..n−1` interpolated and evaluated at
`ω·x_{n−1}` (NOT row `0`). -/
def extRow {n : ℕ} (nodes : Fin n → F) (ω : F) (rows : ℕ → TowerRowVals (K := K) δ) : TowerRowVals (K := K) δ :=
  lagRow (lagW nodes (lastPt nodes ω)) (fun k => rows k)

/-- **The honest residual value at row `j`** (`58` / `59`): `residualVal` of row `j` (with `58/59` zeroed)
and its next row: row `j+1` if `j+1 < n`, else the extrapolation `extRow` of the rows with `58/59` zeroed.
Non-circular: `residualVal` reads no `58/59` column (`residual_reads_class`), and the extrapolated columns
it reads are combinations of the same columns over all rows. -/
def residAt (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ))
    (D : HonestWalk (Quad (algebraMap F K δ))) (n : ℕ)
    (decAt : ℕ → Dec (Quad (algebraMap F K δ))) (vclAt : ℕ → ℕ → F) (nodes : Fin n → F) (ω : F)
    (ch : ℕ → Quad (algebraMap F K δ)) (q : Fin 2) (j : ℕ) : Quad (algebraMap F K δ) :=
  if j + 1 < n then
    residualVal q (rowGen χ αs D n decAt vclAt j 0 0) (rowGen χ αs D n decAt vclAt (j + 1) 0 0) ch
  else
    residualVal q (rowGen χ αs D n decAt vclAt j 0 0)
      (extRow nodes ω (fun k => rowGen χ αs D n decAt vclAt k 0 0)) ch

/-- **The final honest row `j`.** -/
def rowFinal (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ))
    (D : HonestWalk (Quad (algebraMap F K δ))) (n : ℕ)
    (decAt : ℕ → Dec (Quad (algebraMap F K δ))) (vclAt : ℕ → ℕ → F) (nodes : Fin n → F) (ω : F)
    (ch : ℕ → Quad (algebraMap F K δ)) (j : ℕ) : TowerRowVals (K := K) δ :=
  rowGen χ αs D n decAt vclAt j (residAt χ αs D n decAt vclAt nodes ω ch 0 j)
    (residAt χ αs D n decAt vclAt nodes ω ch 1 j)

/-- **The chip's next row of final row `j`**: row `j+1`, or at the last row the extrapolation of the final rows. -/
def nextFinal (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ))
    (D : HonestWalk (Quad (algebraMap F K δ))) (n : ℕ)
    (decAt : ℕ → Dec (Quad (algebraMap F K δ))) (vclAt : ℕ → ℕ → F) (nodes : Fin n → F) (ω : F)
    (ch : ℕ → Quad (algebraMap F K δ)) (j : ℕ) : TowerRowVals (K := K) δ :=
  if j + 1 < n then rowFinal χ αs D n decAt vclAt nodes ω ch (j + 1)
  else extRow nodes ω (rowFinal χ αs D n decAt vclAt nodes ω ch)

/-- The challenge map of the tower source env at the placed challenges (independent of the rows). -/
def chS (b : Basis (Fin 3) F K) (χ : Coins frameVCL K) : ℕ → Quad (algebraMap F K δ) :=
  fun i => if h : i < 12 then (towerGather δ b).chalSlot (chalVQ7T δ b χ) i
    else if 100 ≤ i ∧ i < 164 then
      lamPowVal ((towerGather δ b).chalSlot (chalVQ7T δ b χ) 9) (i - 100) else 0

theorem srcChal_eq (b : Basis (Fin 3) F K) (χ : Coins frameVCL K) (eF : Env F)
    (hch : eF.chal = chalVQ7T δ b χ) :
    (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv.chal = chS (δ := δ) b χ := by
  funext i
  have e : ∀ q : Fin 12, (towerEnv309 δ towerM (gatherEnv b eF) eF).base.chal q =
      (towerGather δ b).chalSlot eF.chal q := fun q => (towerGather δ b).chal_eq eF q
  simp only [Env309.toSourceEnv, CorrectedFinalTypedEnv.toSourceEnv, chS]
  by_cases h : i < 12
  · simp only [h, dite_true]; rw [e ⟨i, h⟩, hch]
  · by_cases h2 : 100 ≤ i ∧ i < 164
    · simp only [h, dite_false, h2, and_self, if_true]
      have := e 9
      rw [this, hch]
      rfl
    · simp [h, h2]


/-! ## 2. `K`-valuedness of the walk fill and `WalkRowEnv` at the final rows -/

section Walk
variable (b : Basis (Fin 3) F K) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ))
  (D : HonestWalk (Quad (algebraMap F K δ))) (n : ℕ)
  (decAt : ℕ → Dec (Quad (algebraMap F K δ))) (vclAt : ℕ → ℕ → F)

theorem im_algebraMap_zero (k : K) : Quad.im (algebraMap F K δ) (algebraMap K (Quad (algebraMap F K δ)) k) = 0 := by
  rw [← Quad.mk_base, Quad.im_mk]

theorem rowGen_walkK (hα : D.α = algebraMap K _ (χ ⟨0, by decide⟩)) (j : ℕ) (hj : j < D.W.length) :
    Quad.im _ (D.cnt (j + 1)) = 0 ∧ Quad.im _ (D.ln (j + 1)) = 0 ∧
      Quad.im _ ((D.cnt (j + 1) - D.ln (j + 1))⁻¹) = 0 := by
  have hαK : Quad.im _ D.α = 0 := by rw [hα]; exact im_algebraMap_zero _
  exact ⟨D.cnt_isK hαK (j + 1) (by omega) (by omega), D.ln_isK hαK (j + 1) (by omega) (by omega),
    D.inv_isK hαK (j + 1) (by omega) (by omega)⟩

theorem chS_six : chS (δ := δ) b χ 6 = algebraMap K (Quad (algebraMap F K δ)) (χ ⟨0, by decide⟩) := by
  simp only [chS, show (6 : ℕ) < 12 by norm_num, dite_true]
  exact chalSlot_six_T δ b χ

/-- **The residual roles are `K`-valued** (role `58` has no Im column). -/
theorem residAt_zero_isK (nodes : Fin n → F) (ω : F) (hα : D.α = algebraMap K _ (χ ⟨0, by decide⟩))
    (hn : n = D.W.length) (j : ℕ) (hj : j < n) :
    Quad.im _ (residAt χ αs D n decAt vclAt nodes ω (chS (δ := δ) b χ) 0 j) = 0 := by
  unfold residAt
  split_ifs with h
  · refine residualVal_zero_isK _ _ _ ?_ ?_ (by rw [chS_six]; exact im_algebraMap_zero _)
    · simpa [rowGen, genRowVals] using (rowGen_walkK χ D hα j (by omega)).1
    · simpa [rowGen, genRowVals] using (rowGen_walkK χ D hα (j + 1) (by omega)).1
  · refine residualVal_zero_isK _ _ _ ?_ ?_ (by rw [chS_six]; exact im_algebraMap_zero _)
    · simpa [rowGen, genRowVals] using (rowGen_walkK χ D hα j (by omega)).1
    · exact lagRow_walk_im _ _ 0 fun k => by
        simpa [rowGen, genRowVals] using (rowGen_walkK χ D hα k (by have := k.isLt; omega)).1

end Walk

section WalkEnv
variable {hC : ℕ} {S : MemShape}
variable (b : Basis (Fin 3) F K) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ))
  (D : HonestWalk (Quad (algebraMap F K δ))) (n : ℕ)
  (decAt : ℕ → Dec (Quad (algebraMap F K δ))) (vclAt : ℕ → ℕ → F)

/-- Off roles `58/59`, a final row agrees with the row with `58/59` zeroed. -/
theorem rowFinal_ext_off (nodes : Fin n → F) (ω : F) (ch : ℕ → Quad (algebraMap F K δ)) (k : ℕ) (r : Fin 63)
    (h58 : r.val ≠ 58) (h59 : r.val ≠ 59) :
    (rowFinal χ αs D n decAt vclAt nodes ω ch k).ext r = (rowGen χ αs D n decAt vclAt k 0 0).ext r := by
  have h58' : (r : ℕ) ≠ 58 := h58
  have h59' : (r : ℕ) ≠ 59 := h59
  simp only [rowFinal, rowGen, genRowVals]
  by_cases hr : (r : ℕ) < 58
  · simp [hr]
  · simp [hr, h58', h59']

/-- **The residual roles of a final row are the `residualVal` of the final row and its chip next row**
(`nextFinal`: row `j+1`, or the extrapolation at the last row) — irrelevance of `58/59`. -/
theorem residAt_eq (nodes : Fin n → F) (ω : F) (ch : ℕ → Quad (algebraMap F K δ)) (q : Fin 2) (j : ℕ) :
    residualVal q (rowFinal χ αs D n decAt vclAt nodes ω ch j)
        (nextFinal χ αs D n decAt vclAt nodes ω ch j) ch =
      residAt χ αs D n decAt vclAt nodes ω ch q j := by
  have hrow := rowFinal_ext_off χ αs D n decAt vclAt nodes ω ch
  unfold residAt nextFinal
  split_ifs with h
  · have := rowSrcEnv_ext5859_irrel (rowFinal χ αs D n decAt vclAt nodes ω ch j)
      (rowFinal χ αs D n decAt vclAt nodes ω ch (j + 1)) (rowGen χ αs D n decAt vclAt j 0 0)
      (rowGen χ αs D n decAt vclAt (j + 1) 0 0) ch rfl rfl rfl (fun r h58 h59 => hrow (j + 1) r h58 h59)
    unfold residualVal
    rw [this]
  · have := rowSrcEnv_ext5859_irrel (rowFinal χ αs D n decAt vclAt nodes ω ch j)
      (extRow nodes ω (rowFinal χ αs D n decAt vclAt nodes ω ch)) (rowGen χ αs D n decAt vclAt j 0 0)
      (extRow nodes ω (fun k => rowGen χ αs D n decAt vclAt k 0 0)) ch rfl rfl rfl (fun r h58 h59 => by
        simp only [extRow, lagRow, hrow _ r h58 h59])
    unfold residualVal
    rw [this]

/-- **The chip next row's `W0` and role `61` are `𝕂`-valued** (both for row `i+1` and for the extrapolation). -/
theorem nextFinal_isK (nodes : Fin n → F) (ω : F) (ch : ℕ → Quad (algebraMap F K δ))
    (hα : D.α = algebraMap K _ (χ ⟨0, by decide⟩)) (hn : n = D.W.length) (i : ℕ) (hi : i < n) :
    Quad.im _ ((nextFinal χ αs D n decAt vclAt nodes ω ch i).walk 0) = 0 ∧
      Quad.im _ ((nextFinal χ αs D n decAt vclAt nodes ω ch i).ext 61) = 0 := by
  unfold nextFinal
  split_ifs with h
  · obtain ⟨hc, hl, -⟩ := rowGen_walkK χ D hα (i + 1) (by omega)
    exact ⟨by simpa [rowFinal, rowGen, genRowVals] using hc, by simpa [rowFinal, rowGen, genRowVals] using hl⟩
  · unfold extRow
    refine ⟨lagRow_walk_im _ _ 0 fun k => ?_, lagRow_ext_im _ _ 61 fun k => ?_⟩
    · simpa [rowFinal, rowGen, genRowVals] using (rowGen_walkK χ D hα k (by have := k.isLt; omega)).1
    · simpa [rowFinal, rowGen, genRowVals] using (rowGen_walkK χ D hα k (by have := k.isLt; omega)).2.1

set_option maxHeartbeats 4000000 in
/-- **`WalkRowEnv` at the final honest rows** (the C2b interface, discharged).  Row `i` of `n = |D.W|`; `hF` the
placement of the final row `i`, `hFn` the placement of its CHIP next row `nextFinal` (row `i+1`, or at the last
row the extrapolation at `ω·x_{n−1}`; from `honestQT_hF` / `honestQT_hFn_final`), `hch`/`hpub` the challenge and
public placement, `hα hγ hroot` the walk coins and the root binding, `hbank` the package's first-row selector bank,
`hv` `V_comp` at every walk row.  Nothing else; no wrap adjacency. -/
theorem walkRowEnv_final (V : VerifierData F K hC S) (hb : V.basis = b) (x : ℕ → F)
    (ρ : Fin 3 → Quad (algebraMap F K δ)) (hn : n = D.W.length) (nodes : Fin n → F) (ω : F)
    (eF : Env F) (i : ℕ) (hi : i < n)
    (hF : ∀ c, SrcRead c → eF.trace c = srcColT b (rowFinal χ αs D n decAt vclAt nodes ω (chS (δ := δ) b χ) i) c)
    (hFn : ∀ c, SrcRead c → eF.traceNext c =
      srcColT b (nextFinal χ αs D n decAt vclAt nodes ω (chS (δ := δ) b χ) i) c)
    (hch : eF.chal = chalVQ7T δ b χ) (hpub : eF.pub = pubCFT δ V x ρ χ)
    (hα : D.α = algebraMap K _ (χ ⟨0, by decide⟩)) (hγ : D.γ = algebraMap K _ (χ ⟨1, by decide⟩))
    (hroot : labelVecOfPub (D.pubAt 0) = ComputeWalkSeed.claimLabelVec (zQuad δ χ) V.claim)
    (hbank : ∀ j, j < 11 → eF.pub (20 + j) = if j = (stateIndex (D.pubAt 0).state : ℕ) then 1 else 0)
    (hv : ∀ j, j < n → Vcomp (towerInputs (δ := δ) χ αs) (D.pubAt j) (decAt j)) :
    WalkRowEnv D (towerEnv309 δ towerM (gatherEnv b eF) eF) i := by
  have hnW : 0 < D.W.length := D.hpos
  obtain ⟨hc, hl, hinv⟩ := rowGen_walkK χ D hα i (by omega)
  have h58 := residAt_zero_isK b χ αs D n decAt vclAt nodes ω hα hn i hi
  have hres0 := residAt_eq χ αs D n decAt vclAt nodes ω (chS (δ := δ) b χ) 0 i
  have hres1 := residAt_eq χ αs D n decAt vclAt nodes ω (chS (δ := δ) b χ) 1 i
  have hchS := srcChal_eq (δ := δ) b χ eF hch
  obtain ⟨hwcK', h61'⟩ := nextFinal_isK χ αs D n decAt vclAt nodes ω (chS (δ := δ) b χ) hα hn i hi
  obtain ⟨v, hvdef⟩ : ∃ v, v = rowFinal χ αs D n decAt vclAt nodes ω (chS (δ := δ) b χ) i := ⟨_, rfl⟩
  obtain ⟨v', hv'def⟩ : ∃ v', v' = nextFinal χ αs D n decAt vclAt nodes ω (chS (δ := δ) b χ) i := ⟨_, rfl⟩
  rw [← hvdef] at hF hres0 hres1
  rw [← hv'def] at hFn hres0 hres1 hwcK' h61'
  have hwcK : Quad.im _ (v.walk 0) = 0 := by simpa [hvdef, rowFinal, rowGen, genRowVals] using hc
  have hr := r5859_of_fill b v v' eF hF hFn hwcK hwcK' h61'
    (by rw [hchS, hres0]; simp [hvdef, rowFinal, rowGen, genRowVals])
    (by rw [hchS, hres1]; simp [hvdef, rowFinal, rowGen, genRowVals])
    (by simpa [hvdef, rowFinal, rowGen, genRowVals] using h58)
  rw [hvdef] at hF
  obtain ⟨wc, wa, e58, e59, e61, e62, e11, e12⟩ := genRow_walkFields b
    (D.pubAt i) (decAt i) (honestEx (towerInputs (δ := δ) χ αs) (D.pubAt i) (decAt i)) i n
    (D.cnt (i + 1)) (D.acc (i + 1)) (D.ln (i + 1)) ((D.cnt (i + 1) - D.ln (i + 1))⁻¹)
    (residAt χ αs D n decAt vclAt nodes ω (chS (δ := δ) b χ) 0 i) (residAt χ αs D n decAt vclAt nodes ω (chS (δ := δ) b χ) 1 i)
    (vclAt i) (fun k => childStateTagCol D.W (i + 1) k) eF hF hc h58 hl hinv
  have hpl := towerEnv309_pub_placement δ b χ V x ρ eF hpub hb
  have hseed : D.seed = seedVCLT δ V.claim χ := by
    rw [genHonestWalk_seed_claim D (zQuad δ χ) V.claim hroot, hα, hγ]; rfl
  have hrowK : ∀ j, j < n →
      Quad.im _ (residAt χ αs D n decAt vclAt nodes ω (chS (δ := δ) b χ) 0 j) = 0 ∧
      Quad.im _ (D.ln (j + 1)) = 0 ∧ Quad.im _ ((D.cnt (j + 1) - D.ln (j + 1))⁻¹) = 0 ∧
      Quad.im _ (D.cnt (j + 1)) = 0 := fun j hj =>
    ⟨residAt_zero_isK b χ αs D n decAt vclAt nodes ω hα hn j hj, (rowGen_walkK χ D hα j (by omega)).2.1,
      (rowGen_walkK χ D hα j (by omega)).2.2, (rowGen_walkK χ D hα j (by omega)).1⟩
  refine ⟨by omega, wc, wa, e61, e62, hr.1, hr.2, e11, by rw [← hn]; exact e12, ?_, ?_, ?_, ?_⟩
  · rw [hpl.1, hα]
  · rw [hpl.2, hseed]
  · intro hlt
    have hlt' : i + 1 < n := by omega
    have hFn' : ∀ c, SrcRead c → eF.traceNext c = srcColT b
        (genRowVals (D.pubAt (i + 1)) (decAt (i + 1))
          (honestEx (towerInputs (δ := δ) χ αs) (D.pubAt (i + 1)) (decAt (i + 1))) (i + 1) n
          (D.cnt (i + 1 + 1)) (D.acc (i + 1 + 1)) (D.ln (i + 1 + 1)) ((D.cnt (i + 1 + 1) - D.ln (i + 1 + 1))⁻¹)
          (residAt χ αs D n decAt vclAt nodes ω (chS (δ := δ) b χ) 0 (i + 1))
          (residAt χ αs D n decAt vclAt nodes ω (chS (δ := δ) b χ) 1 (i + 1))
          (vclAt (i + 1)) (fun k => childStateTagCol D.W (i + 1 + 1) k)) c := by
      rw [hv'def] at hFn
      simp only [nextFinal, if_pos hlt'] at hFn
      exact hFn
    obtain ⟨k58, k61, k62, kc⟩ := hrowK (i + 1) hlt'
    have hwn := genRow_walkNextFields b (D.pubAt (i + 1)) (decAt (i + 1))
      (honestEx (towerInputs (δ := δ) χ αs) (D.pubAt (i + 1)) (decAt (i + 1))) (i + 1) n
      (D.cnt (i + 1 + 1)) (D.acc (i + 1 + 1)) (D.ln (i + 1 + 1)) ((D.cnt (i + 1 + 1) - D.ln (i + 1 + 1))⁻¹)
      (residAt χ αs D n decAt vclAt nodes ω (chS (δ := δ) b χ) 0 (i + 1))
      (residAt χ αs D n decAt vclAt nodes ω (chS (δ := δ) b χ) 1 (i + 1))
      (vclAt (i + 1)) (fun k => childStateTagCol D.W (i + 1 + 1) k) eF hFn' kc k61
    refine ⟨hwn.1, hwn.2.1, hwn.2.2, ?_⟩
    refine nextReads_of_fill b χ D (i + 1) _ eF hFn' hch (fun st => genRowVals_sel _ _ _ _ _ _ _ _ _ _ _ _ _ st)
      hα hγ (fun role c hr hc => ?_) (fun k => ?_)
    · exact nextSrc_of_fill b (D.pubAt (i + 1)) (decAt (i + 1))
        (honestEx (towerInputs (δ := δ) χ αs) (D.pubAt (i + 1)) (decAt (i + 1))) (i + 1) n
        (D.cnt (i + 1 + 1)) (D.acc (i + 1 + 1)) (D.ln (i + 1 + 1)) ((D.cnt (i + 1 + 1) - D.ln (i + 1 + 1))⁻¹)
        _ _ (vclAt (i + 1)) (fun k => childStateTagCol D.W (i + 1 + 1) k) eF (towerInputs (δ := δ) χ αs) hFn' k58 k61 k62
        (hv (i + 1) (by omega)) role c hr hc
    · exact nextTag_honest b (D.pubAt (i + 1)) (decAt (i + 1))
        (honestEx (towerInputs (δ := δ) χ αs) (D.pubAt (i + 1)) (decAt (i + 1))) (i + 1) n
        (D.cnt (i + 1 + 1)) (D.acc (i + 1 + 1)) (D.ln (i + 1 + 1)) ((D.cnt (i + 1 + 1) - D.ln (i + 1 + 1))⁻¹)
        _ _ (vclAt (i + 1)) eF (towerInputs (δ := δ) χ αs) D.W hFn' k58 k61 k62 k
  · intro h0
    subst h0
    refine firstReads_of_fill b χ D eF hch _ rfl hbank hα hγ (fun role c hr hc => ?_) (fun k => ?_)
    · exact firstSrc_of_fill b (D.pubAt 0) (decAt 0)
        (honestEx (towerInputs (δ := δ) χ αs) (D.pubAt 0) (decAt 0)) 0 n
        (D.cnt (0 + 1)) (D.acc (0 + 1)) (D.ln (0 + 1)) ((D.cnt (0 + 1) - D.ln (0 + 1))⁻¹)
        _ _ (vclAt 0) (fun k => childStateTagCol D.W (0 + 1) k) eF (towerInputs (δ := δ) χ αs) hF h58 hl hinv
        (hv 0 hi) role c hr hc
    · exact firstTag_honest b (D.pubAt 0) (decAt 0)
        (honestEx (towerInputs (δ := δ) χ αs) (D.pubAt 0) (decAt 0)) n
        (D.cnt (0 + 1)) (D.acc (0 + 1)) (D.ln (0 + 1)) ((D.cnt (0 + 1) - D.ln (0 + 1))⁻¹)
        _ _ (vclAt 0) eF (towerInputs (δ := δ) χ αs) D.W hF h58 hl hinv k

end WalkEnv

/-! ## 3. The VCL fill: inverses `den′⁻¹` chosen non-circularly -/

section Final
variable (b : Basis (Fin 3) F K) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ))
  (D : HonestWalk (Quad (algebraMap F K δ))) (n : ℕ)
  (decAt : ℕ → Dec (Quad (algebraMap F K δ)))
  (ser : ℕ → F) (ax : ℕ → ℕ) (fIdx vI0 vI1 : ℕ → F) (accX accP : ℕ → Quad (algebraMap F K δ))

/-- The VCL-only columns of row `j` with the three slot inverses ZEROED. -/
def vcl0 (j : ℕ) : ℕ → F := vclFill (δ := δ) b (ser j) (ax j) (fIdx j) (vI0 j) (vI1 j) 0 0 0 (accX j) (accP j)

variable (nodes : Fin n → F) (ω : F) (cv pv : ℕ → F)

/-- The auxiliary rows with zero inverses. -/
def rows0 : Fin n → TowerRowVals (K := K) δ := fun j =>
  rowFinal χ αs D n decAt (vcl0 b ser ax fIdx vI0 vI1 accX accP) nodes ω (chS (δ := δ) b χ) j

/-- The auxiliary trace environment at row `j` (inverses zero). -/
def env0 (j : Fin n) : Env F :=
  Reify.envOfTrace (honestQT b nodes (rows0 b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω) vclWidthT) ω (nodes j) cv pv

/-- **The honest slot inverses**: `den_k′⁻¹` at the auxiliary env (`den_noncircular`: equal to `den_k′` at the final env). -/
def inv0F (j : ℕ) : Quad (algebraMap F K δ) :=
  if h : j < n then (den0Q δ (gatherEnv b (env0 b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv ⟨j, h⟩))
    (env0 b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv ⟨j, h⟩))⁻¹ else 0
def inv1F (j : ℕ) : Quad (algebraMap F K δ) :=
  if h : j < n then (den1Q δ (gatherEnv b (env0 b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv ⟨j, h⟩))
    (env0 b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv ⟨j, h⟩))⁻¹ else 0
def inv2F (j : ℕ) : Quad (algebraMap F K δ) :=
  if h : j < n then (den2Q δ (gatherEnv b (env0 b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv ⟨j, h⟩))
    (env0 b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv ⟨j, h⟩))⁻¹ else 0

/-- **The final VCL-only columns of row `j`.** -/
def vclFinal (j : ℕ) : ℕ → F :=
  vclFill (δ := δ) b (ser j) (ax j) (fIdx j) (vI0 j) (vI1 j)
    (inv0F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv j)
    (inv1F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv j)
    (inv2F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv j) (accX j) (accP j)

/-- **The final honest rows.** -/
def rowsFinal : Fin n → TowerRowVals (K := K) δ := fun j =>
  rowFinal χ αs D n decAt (vclFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) nodes ω
    (chS (δ := δ) b χ) j

end Final

theorem residAt_vcl_irrel (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ))
    (D : HonestWalk (Quad (algebraMap F K δ))) (n : ℕ)
    (decAt : ℕ → Dec (Quad (algebraMap F K δ))) (v1 v2 : ℕ → ℕ → F) (nodes : Fin n → F) (ω : F)
    (ch : ℕ → Quad (algebraMap F K δ)) (q : Fin 2) (j : ℕ) :
    residAt χ αs D n decAt v1 nodes ω ch q j = residAt χ αs D n decAt v2 nodes ω ch q j := rfl

theorem rowFinal_vcl (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ))
    (D : HonestWalk (Quad (algebraMap F K δ))) (n : ℕ)
    (decAt : ℕ → Dec (Quad (algebraMap F K δ))) (v1 v2 : ℕ → ℕ → F) (nodes : Fin n → F) (ω : F)
    (ch : ℕ → Quad (algebraMap F K δ)) (j : ℕ) :
    rowFinal χ αs D n decAt v1 nodes ω ch j = { rowFinal χ αs D n decAt v2 nodes ω ch j with vcl := v1 j } := rfl

/-- Off the inverse columns the VCL fill does not depend on the inverses. -/
theorem vclFill_noninv (b : Basis (Fin 3) F K) (ser : F) (ax : ℕ) (fIdx vI0 vI1 : F)
    (inv0 inv1 inv2 accX accP : Quad (algebraMap F K δ)) (c : ℕ) (hc : ¬ invColT c) :
    vclFill (δ := δ) b ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP c =
      vclFill (δ := δ) b ser ax fIdx vI0 vI1 0 0 0 accX accP c := by
  unfold invColT at hc
  have h1 : ¬ (inv0Base ≤ c ∧ c < inv0Base + 3) := by simp only [inv0Base]; omega
  have h2 : ¬ (lookupInvBase 0 ≤ c ∧ c < lookupInvBase 0 + 3) := by simp only [lookupInvBase]; omega
  have h3 : ¬ (lookupInvBase 1 ≤ c ∧ c < lookupInvBase 1 + 3) := by simp only [lookupInvBase]; omega
  have h4 : ¬ (invImBase 0 ≤ c ∧ c < invImBase 0 + 3) := by simp only [invImBase]; omega
  have h5 : ¬ (invImBase 1 ≤ c ∧ c < invImBase 1 + 3) := by simp only [invImBase]; omega
  have h6 : ¬ (invImBase 2 ≤ c ∧ c < invImBase 2 + 3) := by simp only [invImBase]; omega
  simp only [vclFill, limbAt, h1, h2, h3, h4, h5, h6, dif_neg, not_false_eq_true]

theorem srcColT_vcl_irrel (b : Basis (Fin 3) F K) (v : TowerRowVals (K := K) δ) (w : ℕ → F) :
    srcColT b { v with vcl := w } = srcColT b v := rfl

/-- **`den_noncircular` at the final / auxiliary rows**: the two trace environments agree off the inverse
columns (they differ only in the three inverse fills), so the denominators agree. -/
theorem env_agree_offInv (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)
    (hinj : Function.Injective nodes) (rows rows' : Fin n → TowerRowVals (K := K) δ)
    (hsrc : ∀ i, srcColT b (rows i) = srcColT b (rows' i))
    (hvcl : ∀ i c, ¬ invColT c → (rows i).vcl c = (rows' i).vcl c)
    (ω : F) (cv pv : ℕ → F) (i : Fin n) (c : ℕ) (hc : ¬ invColT c) :
    (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv).trace c =
      (Reify.envOfTrace (honestQT b nodes rows' vclWidthT) ω (nodes i) cv pv).trace c := by
  by_cases hw : c < vclWidthT
  · rw [env_honestQT_trace b nodes hinj rows ω cv pv i hw, env_honestQT_trace b nodes hinj rows' ω cv pv i hw]
    unfold vclColT
    by_cases h1 : c < 202
    · simp only [h1, if_true]; exact congrFun (hsrc i) c
    · by_cases h2 : (208 ≤ c ∧ c < 214) ∨ (232 ≤ c ∧ c < 394)
      · simp only [h1, h2, if_false, if_true]; exact congrFun (hsrc i) (c + 95)
      · simp only [h1, h2, if_false]; exact hvcl i c hc
  · simp [Reify.envOfTrace, hw]

theorem envOfTrace_chal_irrel {w w' : ℕ} (P : Fin w → Polynomial F) (P' : Fin w' → Polynomial F)
    (ω x x' : F) (cv pv : ℕ → F) :
    (Reify.envOfTrace P ω x cv pv).chal = (Reify.envOfTrace P' ω x' cv pv).chal := rfl

/-- **The slot inverses of the final rows are `den′⁻¹` at the final env** (`den_noncircular`). -/
theorem inv_final_eq (b : Basis (Fin 3) F K) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ))
    (D : HonestWalk (Quad (algebraMap F K δ))) (n : ℕ)
    (decAt : ℕ → Dec (Quad (algebraMap F K δ)))
    (ser : ℕ → F) (ax : ℕ → ℕ) (fIdx vI0 vI1 : ℕ → F) (accX accP : ℕ → Quad (algebraMap F K δ))
    (nodes : Fin n → F) (hinj : Function.Injective nodes) (ω : F) (cv pv : ℕ → F) (i : Fin n) :
    inv0F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv i =
        (den0Q δ (gatherEnv b (Reify.envOfTrace (honestQT b nodes
          (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))
          (Reify.envOfTrace (honestQT b nodes
          (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))⁻¹ ∧
    inv1F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv i =
        (den1Q δ (gatherEnv b (Reify.envOfTrace (honestQT b nodes
          (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))
          (Reify.envOfTrace (honestQT b nodes
          (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))⁻¹ ∧
    inv2F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv i =
        (den2Q δ (gatherEnv b (Reify.envOfTrace (honestQT b nodes
          (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))
          (Reify.envOfTrace (honestQT b nodes
          (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))⁻¹ := by
  have hc : ∀ c, ¬ invColT c → (env0 b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv i).trace c =
      (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv).trace c :=
    fun c hc => env_agree_offInv b nodes hinj
      (rows0 b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω)
      (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv)
      (fun j => by
        show srcColT b (rowFinal χ αs D n decAt (vcl0 b ser ax fIdx vI0 vI1 accX accP) nodes ω (chS (δ := δ) b χ) j) =
          srcColT b (rowFinal χ αs D n decAt (vclFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv)
            nodes ω (chS (δ := δ) b χ) j)
        rw [rowFinal_vcl χ αs D n decAt (vcl0 b ser ax fIdx vI0 vI1 accX accP)
          (vclFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) nodes ω, srcColT_vcl_irrel])
      (fun j c hc' => (vclFill_noninv b _ _ _ _ _ _ _ _ _ _ c hc').symm) ω cv pv i c hc
  obtain ⟨d0, d1, d2⟩ := den_noncircular (δ := δ) (b := b)
    (eF := env0 b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv i)
    (eF' := Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv) hc (envOfTrace_chal_irrel _ _ _ _ _ _ _)
  refine ⟨?_, ?_, ?_⟩
  · simp only [inv0F, dif_pos i.isLt]; rw [d0]
  · simp only [inv1F, dif_pos i.isLt]; rw [d1]
  · simp only [inv2F, dif_pos i.isLt]; rw [d2]

/-- **`hFn` at row `i` of the final carrier, with no wrap**: for `i+1 < n` (adjacency `hadjC`, the
package's `AdjacentC` shape) the next row is row `i+1`; at the last row it is the extrapolation `extRow`. -/
theorem honestQT_hFn_final (b : Basis (Fin 3) F K) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ))
    (D : HonestWalk (Quad (algebraMap F K δ))) (n : ℕ)
    (decAt : ℕ → Dec (Quad (algebraMap F K δ)))
    (ser : ℕ → F) (ax : ℕ → ℕ) (fIdx vI0 vI1 : ℕ → F) (accX accP : ℕ → Quad (algebraMap F K δ))
    (nodes : Fin n → F) (hinj : Function.Injective nodes) (ω : F) (cv pv : ℕ → F)
    (hadjC : ∀ (j : Fin n) (hj : (j : ℕ) + 1 < n), nodes ⟨(j : ℕ) + 1, hj⟩ = ω * nodes j) (i : Fin n) :
    ∀ c, SrcRead c → (pullEnv (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv)).traceNext c =
      srcColT b (nextFinal χ αs D n decAt (vclFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv)
        nodes ω (chS (δ := δ) b χ) i) c := by
  intro c hc
  by_cases h : (i : ℕ) + 1 < n
  · rw [honestQT_hFn b nodes hinj _ ω cv pv i ⟨(i : ℕ) + 1, h⟩ (hadjC i h).symm c hc]
    simp only [nextFinal, if_pos h]
    rfl
  · rw [pullNext_honestQT_lag b nodes _ ω (nodes i) cv pv c hc]
    have h0 : 0 < n := by have := i.isLt; omega
    have hpt : ω * nodes i = lastPt nodes ω := by
      simp only [lastPt, dif_pos h0]
      congr 2
      apply Fin.ext
      simp only
      omega
    rw [hpt]
    simp only [nextFinal, if_neg h]
    rfl

/-! ## 4. The assembled row -/

section Assembled
open Nock.NockVMROM.Thm54.TraceGen
variable {hC : ℕ} {S : MemShape}

set_option maxHeartbeats 8000000 in
/-- **The assembled honest row.**  At row `i` of the final carrier `rowsFinal` (the honest
`genRowVals` rows with tags `childStateTagCol`, walk values of `D`, the non-circular residual roles and
inverses `den′⁻¹`), five gate families hold:

* (a) every walk gate (`walk_row_holds_of_order`);
* (b) every row-local kept core gate (`honest_rowMatch_feeds_rowLocal`);
* (c) the three slot lookup gates (`lookupGatesT_honest`);
* (d) the serial gates, (e) the axis gates.

Hypotheses left (all C4 / C2d / tree-link): `hord`; `hv`/`hwf`/`hz` (`V_comp`, `WF`, `z′ ≠ 0` from `SeedGood` +
`rlc5Holds`: `gen_vcomp_wf`); the pole conditions `hne0 hp he h6 h9`; `hadjC` (the package's `AdjacentC`
shape, `i+1 < n` only — the last row's next env is the extrapolation, no wrap);
`hch`/`hpub`/`hx0` (challenge / public placement); `hα hγ hroot` (walk coins, root binding:
`genHonestWalk_hroot`); `hser`; and the tree links `hpubg hdecg hshape hax` for the axis gate
(`gen_ax_dec`).  The accumulator gates are NOT in this theorem (item 2). -/
theorem assembled_row (b : Basis (Fin 3) F K) (V : VerifierData F K hC S) (hb : V.basis = b) (x : ℕ → F)
    (ρ : Fin 3 → Quad (algebraMap F K δ))
    (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ))
    (D : HonestWalk (Quad (algebraMap F K δ))) (n : ℕ)
    (decAt : ℕ → Dec (Quad (algebraMap F K δ)))
    (ser : ℕ → F) (ax : ℕ → ℕ) (fIdx vI0 vI1 : ℕ → F) (accX accP : ℕ → Quad (algebraMap F K δ))
    (nodes : Fin n → F) (hinj : Function.Injective nodes) (ω : F) (cv pv : ℕ → F)
    (hn : n = D.W.length)
    (hadjC : ∀ (j : Fin n) (hj : (j : ℕ) + 1 < n), nodes ⟨(j : ℕ) + 1, hj⟩ = ω * nodes j) (i : Fin n)
    (hch : (pullEnv (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv)).chal =
        chalVQ7T δ b χ)
    (hpub : (pullEnv (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv)).pub =
        pubCFT δ V x ρ χ)
    (hx0 : ∀ j, j < 11 → x (20 + j) = if j = (stateIndex (D.pubAt 0).state : ℕ) then 1 else 0)
    (hα : D.α = algebraMap K _ (χ ⟨0, by decide⟩)) (hγ : D.γ = algebraMap K _ (χ ⟨1, by decide⟩))
    (hroot : labelVecOfPub (D.pubAt 0) = ComputeWalkSeed.claimLabelVec (zQuad δ χ) V.claim)
    (hord : D.W.length ≤ orderOf D.α)
    (hv : ∀ j, j < n → Vcomp (towerInputs (δ := δ) χ αs) (D.pubAt j) (decAt j))
    (hwf : ∀ j, j < n → WF (towerInputs (δ := δ) χ αs) (D.pubAt j))
    (hz : zQuad δ χ ≠ 0)
    (hser : ∀ j, ser j = (j : F))
    (hne0 : den0Q δ (gatherEnv b (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))
        (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv) ≠ 0)
    (hp : (stateIndex (D.pubAt i).state : ℕ) = 0 → FiniteIO.compress
      (coinsQ δ (gatherEnv b (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))
        (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))
      (recValQ δ (gatherEnv b (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))
        (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv)
        op0PathRec) ≠ 0)
    (he : (stateIndex (D.pubAt i).state : ℕ) ∈ slot1ExportSels → FiniteIO.compress
      (coinsQ δ (gatherEnv b (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))
        (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))
      (recValQ δ (gatherEnv b (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))
        (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv)
        tailRec) ≠ 0)
    (h6 : (stateIndex (D.pubAt i).state : ℕ) = 6 → FiniteIO.compress
      (coinsQ δ (gatherEnv b (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))
        (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))
      (recValQ δ (gatherEnv b (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))
        (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv)
        ttRec) ≠ 0)
    (h9 : (stateIndex (D.pubAt i).state : ℕ) = 9 → FiniteIO.compress
      (coinsQ δ (gatherEnv b (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))
        (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))
      (recValQ δ (gatherEnv b (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))
        (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv)
        op9PathRec) ≠ 0)
    (g : GenComputeRow (Quad (algebraMap F K δ))) (hshape : NodeAxisInFormula g)
    (hpubg : D.pubAt i = (renderNode (zQuad δ χ) αs g).row.2.2.1)
    (hdecg : decAt i = (renderNode (zQuad δ χ) αs g).row.2.2.2)
    (hax : ax i = honestAx g.skel) :
    WalkGatesHold (towerEnv309 δ towerM (gatherEnv b (pullEnv (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv)))
        (pullEnv (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))) ∧
    (∀ g ∈ keptCoreIdsQ7, g.val < 72 → towerHolds δ (gatherEnv b (pullEnv (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv)))
        (pullEnv (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv))
        (coreTarget g)) ∧
    (∀ g ∈ lookupGatesT b δ, g.eval (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv) = 0) ∧
    (∀ g ∈ (serialGates : List (CoeffExpr F)), g.eval (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv) = 0) ∧
    (∀ g ∈ axGates b, g.eval (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv) = 0) ∧
    (∀ g ∈ (axImGates : List (CoeffExpr F)), g.eval (Reify.envOfTrace (honestQT b nodes
        (rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv) vclWidthT) ω (nodes i) cv pv) = 0) := by
  set R := rowsFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv with hRdef
  set E := Reify.envOfTrace (honestQT b nodes R vclWidthT) ω (nodes i) cv pv with hEdef
  set VF := vclFinal b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv with hVFdef
  have hF := honestQT_hF b nodes hinj R ω cv pv i
  have hFn := honestQT_hFn_final b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes hinj ω cv pv hadjC i
  have hbank : ∀ j, j < 11 → (pullEnv E).pub (20 + j) =
      if j = (stateIndex (D.pubAt 0).state : ℕ) then 1 else 0 := by
    intro j hj
    rw [hpub, pubCFT_bank δ χ V x ρ _ (Or.inr (by omega)), hx0 j hj]
  have WR := walkRowEnv_final b χ αs D n decAt VF V hb x ρ hn nodes ω (pullEnv E) i i.isLt hF hFn hch hpub hα hγ
    hroot hbank hv
  obtain ⟨hc0, hl0, hinv0⟩ := rowGen_walkK χ D hα i (by omega)
  have h58 := residAt_zero_isK b χ αs D n decAt VF nodes ω hα hn i i.isLt
  have hRi : R i = genRowVals (D.pubAt i) (decAt i)
      (honestEx (towerInputs (δ := δ) χ αs) (D.pubAt i) (decAt i)) i n
      (D.cnt (i + 1)) (D.acc (i + 1)) (D.ln (i + 1)) ((D.cnt (i + 1) - D.ln (i + 1))⁻¹)
      (residAt χ αs D n decAt VF nodes ω (chS (δ := δ) b χ) 0 i) (residAt χ αs D n decAt VF nodes ω (chS (δ := δ) b χ) 1 i)
      (VF i) (fun k => childStateTagCol D.W (i + 1) k) := rfl
  have hiN : (i : ℕ) < n := i.isLt
  refine ⟨walk_row_holds_of_order WR hord, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg hlt
    exact honest_rowMatch_feeds_rowLocal b χ αs (D.pubAt i) (decAt i) i n
      (D.cnt (i + 1)) (D.acc (i + 1)) (D.ln (i + 1)) ((D.cnt (i + 1) - D.ln (i + 1))⁻¹)
      (residAt χ αs D n decAt VF nodes ω (chS (δ := δ) b χ) 0 i) (residAt χ αs D n decAt VF nodes ω (chS (δ := δ) b χ) 1 i)
      (VF i) (fun k => childStateTagCol D.W (i + 1) k) (pullEnv E) hF hch (hv i hiN) (hwf i hiN) hz h58 hl0 hinv0 g hg hlt
  · have hs : ∀ j, j < 11 → E.trace j = if j = (stateIndex (D.pubAt i).state : ℕ) then 1 else 0 := by
      intro j hj
      rw [hEdef, env_honestQT_trace b nodes hinj R ω cv pv i (by show j < 410; omega)]
      simp only [vclColT, show j < 202 by omega, if_true, srcColT, show j < 13 by omega, dif_pos, hRi]
      simp [genRowVals, hj]
    have hinvQ := vclFill_invQ b nodes hinj R ω cv pv i (ser i) (ax i) (fIdx i) (vI0 i) (vI1 i)
      (inv0F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv i)
      (inv1F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv i)
      (inv2F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv i) (accX i) (accP i)
      (by rw [hRdef]; rfl)
    obtain ⟨e0, e1, e2⟩ := inv_final_eq b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes hinj ω cv pv i
    have hz1 : E.trace z1Col = 0 ∨ E.trace z1Col = 1 := by
      rw [hEdef, env_honestQT_trace b nodes hinj R ω cv pv i (by decide : z1Col < vclWidthT)]
      simp only [vclColT, z1Col, show ¬ (409 < 202) by omega, show ¬ ((208 ≤ 409 ∧ 409 < 214) ∨ (232 ≤ 409 ∧ 409 < 394)) by omega,
        if_false]
      rw [hRi]
      show VF i 409 = 0 ∨ VF i 409 = 1
      rw [show VF i 409 = _ from vclFill_z1 (δ := δ) b _ (ax i) _ _ _ _ _ _ _ _]
      split_ifs <;> simp
    exact lookupGatesT_honest δ b E hz1 _ (stateIndex (D.pubAt i).state).isLt hs
      (by rw [hinvQ.1, e0]) (by rw [hinvQ.2.1, e1]) (by rw [hinvQ.2.2, e2]) hne0 hp he h6 h9
  · exact serialGates_honestQT b nodes hinj R ω cv pv i
      (by rw [hRi]; simp [genRowVals]) (by rw [hRi]; simp [genRowVals])
      (fun j => by
        show vclFill (δ := δ) b (ser j) (ax j) (fIdx j) (vI0 j) (vI1 j)
          (inv0F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv j)
          (inv1F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv j)
          (inv2F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv j) (accX j) (accP j) serialCol = _
        rw [vclFill_serial, hser])
      (if h : (i : ℕ) + 1 < n then ⟨(i : ℕ) + 1, h⟩ else i)
      (fun hl => by simp only [dif_pos hl]; exact ⟨(hadjC i hl).symm, trivial⟩)
  · refine (honest_ax_of_gen b nodes hinj R ω cv pv i (zQuad δ χ) αs g hshape
      (honestEx (towerInputs (δ := δ) χ αs) (D.pubAt i) (decAt i)) i n
      (D.cnt (i + 1)) (D.acc (i + 1)) (D.ln (i + 1)) ((D.cnt (i + 1) - D.ln (i + 1))⁻¹)
      (residAt χ αs D n decAt VF nodes ω (chS (δ := δ) b χ) 0 i) (residAt χ αs D n decAt VF nodes ω (chS (δ := δ) b χ) 1 i)
      (VF i) (fun k => childStateTagCol D.W (i + 1) k) ?_ ?_).1
    · rw [← hpubg, ← hdecg]; exact hRi
    · show vclFill (δ := δ) b (ser i) (ax i) (fIdx i) (vI0 i) (vI1 i)
        (inv0F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv i)
        (inv1F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv i)
        (inv2F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv i) (accX i) (accP i) 221 = _
      rw [show (221 : ℕ) = axCol from rfl, vclFill_ax, hax]
  · refine (honest_ax_of_gen b nodes hinj R ω cv pv i (zQuad δ χ) αs g hshape
      (honestEx (towerInputs (δ := δ) χ αs) (D.pubAt i) (decAt i)) i n
      (D.cnt (i + 1)) (D.acc (i + 1)) (D.ln (i + 1)) ((D.cnt (i + 1) - D.ln (i + 1))⁻¹)
      (residAt χ αs D n decAt VF nodes ω (chS (δ := δ) b χ) 0 i) (residAt χ αs D n decAt VF nodes ω (chS (δ := δ) b χ) 1 i)
      (VF i) (fun k => childStateTagCol D.W (i + 1) k) ?_ ?_).2
    · rw [← hpubg, ← hdecg]; exact hRi
    · show vclFill (δ := δ) b (ser i) (ax i) (fIdx i) (vI0 i) (vI1 i)
        (inv0F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv i)
        (inv1F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv i)
        (inv2F b χ αs D n decAt ser ax fIdx vI0 vI1 accX accP nodes ω cv pv i) (accX i) (accP i) 221 = _
      rw [show (221 : ℕ) = axCol from rfl, vclFill_ax, hax]

end Assembled

end Rows

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
