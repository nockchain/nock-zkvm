import Nock.NockVMROM.Thm54.VclL.Compute.TowerC2cBase
import Nock.NockVMROM.Thm54.VclL.Compute.TowerGenTable
import Nock.NockVMROM.Thm54.TraceGen.GenAirTransport
import Nock.NockVMROM.Thm54.TraceGen.GenWF

/-!
# Generator → honest tower row, and the C2a / C2c hypotheses discharged

* `honestOverlay`: the un-hosted overlay of a row (walk count/acc live in `W0/W1`, child-state tags
  hosted as deployed (the tag vector `tg` is a parameter, C1g: instantiate at `childStateTagCol W (i+1) k`), IO vestige `ioAcc = denoms = 0`).
* `honestEx`: the auxiliary witness `ex` by `Classical.choose` from `computeAIR_iff_Vcomp`.
* `genRowVals`: one honest `TowerRowVals`: base = one-hot state + first/last masks, roles `0..57` =
  `coreExtensionValue` of the un-hosted 309 row, `58/59` = the residual values, `60 = 0`, `61/62` =
  walk `ln` / `inv`, `W0/W1` = walk count/acc.  The walk and residual values are parameters (the C2b
  interface, `WalkGatesT.HonestWalk`).
* `honestSrcEnv`: the tower base env with publics zeroed and the dead read set (roles `54/55`,
  challenge `0`) filled by a free generator `α*` and the row's `ln_prev / ln`.
* **`gen_vcomp_wf`**: `V_comp` (re-keyed to `(χ₈,χ₉,χ₁₀)`) and `WF` at every BFS row of the AIR-ordered
  generated tree, from `SeedGood` and the named honestBad condition `rlc5Holds χ₈ χ₉ χ₁₀`.
* `genRow_baseCells`, `genRow_eq_hyps`: C1b's `HonestBaseCells` and the `eq22_of_cells` side
  conditions, from the row index and the states of rows `0` and `n − 1`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.ComputeTable Nock.Reified Module
open Nock.NockVMROM.Thm54.OptimizedComputeCodec Nock.NockVMROM.Thm54.OptimizedComputeOverlay
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7
open Nock.NockVMROM.Thm54.ComputePaperPacking (OneHotSelector)

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

/-! ## 1. Overlay and auxiliary witness -/

section Row
variable {L : Type} [Field L]

/-- **The honest un-hosted overlay**: tags as `optionTagOf` decodes them, IO vestige zero; walk
count/acc are carried by `W0/W1`, so they are `0` here (the 309 encoding ignores them). -/
def honestOverlay (tg : Fin 3 → L) (_pub : Pub L) : SampledOverlayValues L :=
  { walkCount := 0, walkAcc := 0
    sf1_st := tg 0
    sf2_st := tg 1
    sf3_st := tg 2
    ioAcc := 0, denom0 := 0, denom1 := 0, denom2 := 0 }

/-- **The honest auxiliary witness** (`cons_inv`, `inv_gen`) by choice. -/
def honestEx (inp : Inputs L) (pub : Pub L) (dec : Dec L) : Extra L := by
  classical
  exact if h : ∃ ex : Extra L, ∀ c ∈ Nock.Reified.computeAIR.constraints,
      c.expr.eval (computeEnvFull inp (opSel pub.state) pub dec ex) = 0 then h.choose else ⟨0, 0⟩

theorem honestEx_air {inp : Inputs L} {pub : Pub L} {dec : Dec L} (wf : WF inp pub)
    (hv : Vcomp inp pub dec) (hz : inp.z ≠ 0) :
    ∀ c ∈ Nock.Reified.computeAIR.constraints,
      c.expr.eval (computeEnvFull inp (opSel pub.state) pub dec (honestEx inp pub dec)) = 0 := by
  have h := (computeAIR_iff_Vcomp inp pub dec wf).mpr ⟨hv, hz⟩
  unfold honestEx
  simp only [dif_pos h]
  exact h.choose_spec

end Row

/-! ## 2. The honest tower row -/

theorem opCol_eq_stateIndex : ∀ st : State, Nock.Reified.opCol st = (stateIndex st : ℕ) := by
  decide

theorem stateIndex_eq_iff : ∀ s t : State, ((stateIndex s : ℕ) = stateIndex t) ↔ s = t := by
  decide

/-- The roles without an Im column. -/
theorem towerM_ext_none_roles : ∀ r : Fin 63, towerM.ext r = none →
    r.val = 32 ∨ r.val = 33 ∨ r.val = 34 ∨ r.val = 35 ∨ r.val = 54 ∨ r.val = 55 ∨
      r.val = 58 ∨ r.val = 60 ∨ r.val = 61 ∨ r.val = 62 := by
  decide +kernel

section Gen
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **The generator → `TowerRowVals` map** for row `i` of `n`.  `wc wa` are the walk count/acc
(`W0/W1`), `wln winv` the walk line and queue inverse (roles `61/62`), `r58 r59` the residual values
(roles `58/59`), `vcl` the VCL-only columns. -/
def genRowVals (pub : Pub (Quad (algebraMap F K δ))) (dec : Dec (Quad (algebraMap F K δ)))
    (ex : Extra (Quad (algebraMap F K δ))) (i n : ℕ)
    (wc wa wln winv r58 r59 : Quad (algebraMap F K δ)) (vcl : ℕ → F) (tg : Fin 3 → Quad (algebraMap F K δ)) :
    TowerRowVals (K := K) δ where
  base := fun j =>
    if (j : ℕ) < 11 then (if (j : ℕ) = (stateIndex pub.state : ℕ) then 1 else 0)
    else if (j : ℕ) = 11 then (if i = 0 then 1 else 0)
    else (if i + 1 = n then 1 else 0)
  ext := fun r =>
    if h : (r : ℕ) < 58 then
      coreExtensionValue (row309 (F := F) pub dec ex (honestOverlay tg pub)) ⟨r, h⟩
    else if (r : ℕ) = 58 then r58 else if (r : ℕ) = 59 then r59
    else if (r : ℕ) = 60 then 0 else if (r : ℕ) = 61 then wln else winv
  walk := ![wc, wa]
  vcl := vcl

variable (pub : Pub (Quad (algebraMap F K δ))) (dec : Dec (Quad (algebraMap F K δ)))
  (ex : Extra (Quad (algebraMap F K δ))) (i n : ℕ)
  (wc wa wln winv r58 r59 : Quad (algebraMap F K δ)) (vcl : ℕ → F) (tg : Fin 3 → Quad (algebraMap F K δ))

set_option maxHeartbeats 2000000 in
/-- **IO vestige**: roles `32..35` and `60` of the honest row are zero. -/
theorem genRowVals_vestige :
    (genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg).ext 32 = 0 ∧
    (genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg).ext 33 = 0 ∧
    (genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg).ext 34 = 0 ∧
    (genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg).ext 35 = 0 ∧
    (genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg).ext 60 = 0 := by
  cases hs : pub.state <;>
    simp [genRowVals, coreExtensionValue, row309, sampledEncode309, sampledEncodeExtension309,
      sampledEncodeExtension, honestOverlay, overlayRoleA, overlayRoleB, overlayDenoms,
      fpCoordinate, hs]

theorem genRowVals_ext_lt (r : ℕ) (h : r < 58) :
    (genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg).ext ⟨r, by omega⟩ =
      coreExtensionValue (row309 (F := F) pub dec ex (honestOverlay tg pub)) ⟨r, h⟩ := by
  simp [genRowVals, h]

/-- **The `𝕂`-valuedness the placement needs**: every role without an Im column has zero Im part,
given that the walk line / inverse and residual `58` are `𝕂`-valued, except the dead roles `54/55`. -/
theorem genRowVals_imZero
    (h58 : Quad.im _ r58 = 0) (h61 : Quad.im _ wln = 0) (h62 : Quad.im _ winv = 0)
    (r : Fin 63) (h54 : r.val ≠ 54) (h55 : r.val ≠ 55) (hn : towerM.ext r = none) :
    Quad.im _ ((genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg).ext r) = 0 := by
  obtain ⟨v32, v33, v34, v35, v60⟩ := genRowVals_vestige pub dec ex i n wc wa wln winv r58 r59 vcl tg
  rcases towerM_ext_none_roles r hn with h | h | h | h | h | h | h | h | h | h
  all_goals first
    | (exact absurd h h54) | (exact absurd h h55)
    | (have e : r = 32 := Fin.ext h; rw [e, v32]; exact quad_im_zero _)
    | (have e : r = 33 := Fin.ext h; rw [e, v33]; exact quad_im_zero _)
    | (have e : r = 34 := Fin.ext h; rw [e, v34]; exact quad_im_zero _)
    | (have e : r = 35 := Fin.ext h; rw [e, v35]; exact quad_im_zero _)
    | (have e : r = 60 := Fin.ext h; rw [e, v60]; exact quad_im_zero _)
    | (have e : r = 58 := Fin.ext h; subst e; simpa [genRowVals] using h58)
    | (have e : r = 61 := Fin.ext h; subst e; simpa [genRowVals] using h61)
    | (have e : r = 62 := Fin.ext h; subst e; simpa [genRowVals] using h62)

end Gen

/-! ## 3. The source env of `RowMatch`, and `AgreeOff` against the tower env -/

section SrcEnv
variable {F L : Type} [Field F] [Field L]

/-- **The honest source env**: the tower base env `T` with zero publics and the dead read set
filled — challenge `0` by the free generator `α*`, roles `54/55` by the row's `ln_prev / ln`. -/
def honestSrcEnv (T : CorrectedFinalTypedEnv F L) (αs lnp ln : L) : CorrectedFinalTypedEnv F L :=
  { T with
    extensionPublic := fun _ => 0
    scalarPublic := fun _ => 0
    extTrace := fun r => if (r : ℕ) = 54 then lnp else if (r : ℕ) = 55 then ln else T.extTrace r
    chal := fun s => if (s : ℕ) = 0 then αs else T.chal s }

structure AgreeOffT (E₁ E₂ : CorrectedFinalTypedEnv F L) : Prop where
  baseTrace : E₁.baseTrace = E₂.baseTrace
  baseTraceNext : E₁.baseTraceNext = E₂.baseTraceNext
  extTraceNext : E₁.extTraceNext = E₂.extTraceNext
  certBase : E₁.certBase = E₂.certBase
  certExt : E₁.certExt = E₂.certExt
  expCol : E₁.expCol = E₂.expCol
  ext : ∀ r : Fin 63, r.val ≠ 54 → r.val ≠ 55 → E₁.extTrace r = E₂.extTrace r
  chal : ∀ s : Fin 12, s.val ≠ 0 → s.val ≠ 9 → E₁.chal s = E₂.chal s

theorem agreeOffT_honestSrc (T : CorrectedFinalTypedEnv F L) (αs lnp ln : L) :
    AgreeOffT T (honestSrcEnv T αs lnp ln) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl,
    fun r h54 h55 => by simp [honestSrcEnv, h54, h55],
    fun s h0 _ => by simp only [honestSrcEnv, if_neg h0]⟩

theorem honestSrcEnv_pub [Algebra F L] (T : CorrectedFinalTypedEnv F L) (αs lnp ln : L) (j : ℕ) :
    (honestSrcEnv T αs lnp ln).toSourceEnv.pub j = 0 := by
  simp [honestSrcEnv, CorrectedFinalTypedEnv.toSourceEnv]

structure RowMatchT (env : Env L) (inp : Inputs L) (st : State) (pub : Pub L) (dec : Dec L)
    (ex : Extra L) : Prop where
  table : ∀ j, j < 94 → (Env.ofSubst computeSubst env).trace j =
    (computeEnvFull inp (opSel st) pub dec ex).trace j
  chal : ∀ j, j < 5 → (Env.ofSubst computeSubst env).chal j =
    (computeEnvFull inp (opSel st) pub dec ex).chal j
  pubs : ∀ j, env.pub j = (computeEnvFull inp (opSel st) pub dec ex).pub j
  air : ∀ c ∈ Nock.Reified.computeAIR.constraints,
    c.expr.eval (computeEnvFull inp (opSel st) pub dec ex) = 0
  oneHot : OneHotSelector env st

end SrcEnv

/-! ## 4. `RowMatch` and `AgreeOff` at every honest row -/

section Match
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- The honest compute inputs at the tower: the free generator `α*`, `z′ = (χ₂, χ₃)`, and the
equality coins re-keyed to `χ₈, χ₉, χ₁₀`. -/
def towerInputs (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ)) :
    Inputs (Quad (algebraMap F K δ)) :=
  ⟨αs, zQuad δ χ, algebraMap K _ (χ ⟨8, by decide⟩), algebraMap K _ (χ ⟨9, by decide⟩),
    algebraMap K _ (χ ⟨10, by decide⟩)⟩

set_option maxHeartbeats 4000000 in
/-- **C1c item 2: `RowMatch` at an honest row, `AgreeOff` against the tower env.**  The tower
fill of the row is `genRowVals` (`hF`: the pull-back reads its source fill; `hch`: challenges
`chalVQ7T`).  Hypotheses on the row: `V_comp` and `WF` at the re-keyed inputs, `z′ ≠ 0`, and the
three `𝕂`-valued walk/residual roles. -/
theorem honest_rowMatch (b : Basis (Fin 3) F K) (χ : Coins frameVCL K)
    (αs : Quad (algebraMap F K δ))
    (pub : Pub (Quad (algebraMap F K δ))) (dec : Dec (Quad (algebraMap F K δ))) (i n : ℕ)
    (wc wa wln winv r58 r59 : Quad (algebraMap F K δ)) (vcl : ℕ → F) (tg : Fin 3 → Quad (algebraMap F K δ)) (eF : Env F)
    (hF : ∀ c, SrcRead c → eF.trace c = srcColT b
      (genRowVals pub dec (honestEx (towerInputs (δ := δ) χ αs) pub dec) i n wc wa wln winv r58 r59 vcl tg) c)
    (hch : eF.chal = chalVQ7T δ b χ)
    (hv : Vcomp (towerInputs (δ := δ) χ αs) pub dec) (wf : WF (towerInputs (δ := δ) χ αs) pub)
    (hz : zQuad δ χ ≠ 0)
    (h58 : Quad.im _ r58 = 0) (h61 : Quad.im _ wln = 0) (h62 : Quad.im _ winv = 0) :
    RowMatchT (honestSrcEnv (towerEnv309 δ towerM (gatherEnv b eF) eF).base αs pub.ln_prev pub.ln
        ).toSourceEnv (towerInputs (δ := δ) χ αs) pub.state pub dec (honestEx (towerInputs (δ := δ) χ αs) pub dec) ∧
      AgreeOffT (towerEnv309 δ towerM (gatherEnv b eF) eF).base
        (honestSrcEnv (towerEnv309 δ towerM (gatherEnv b eF) eF).base αs pub.ln_prev pub.ln) := by
  set inp := towerInputs (δ := δ) χ αs with hinp
  set ex := honestEx inp pub dec with hex
  set v := genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg with hvdef
  set T := (towerEnv309 δ towerM (gatherEnv b eF) eF).base with hT
  set E := honestSrcEnv T αs pub.ln_prev pub.ln with hE
  have hchal := towerEnv309_chal_placement δ b χ eF hch
  -- selectors
  have hsel : ∀ st, E.toSourceEnv.trace (Nock.Reified.opCol st) = if st = pub.state then 1 else 0 := by
    intro st
    have hlt : Nock.Reified.opCol st < 11 := by rw [opCol_eq_stateIndex]; exact (stateIndex st).isLt
    have hb := towerEnv309_base_of_src b v eF hF ⟨Nock.Reified.opCol st, by omega⟩
    simp only [E, honestSrcEnv, CorrectedFinalTypedEnv.toSourceEnv, show Nock.Reified.opCol st < 13 by omega,
      dif_pos]
    rw [show (⟨Nock.Reified.opCol st, by omega⟩ : Fin 13) = ⟨Nock.Reified.opCol st, by omega⟩ from rfl]
    erw [hb]
    simp only [v, genRowVals, hlt, if_true]
    by_cases hs : st = pub.state <;> simp [hs, opCol_eq_stateIndex, stateIndex_eq_iff]
  -- the 58 core roles
  have hext : ∀ j : Fin 58, E.toSourceEnv.trace (13 + j) =
      coreExtensionValue (row309 (F := F) pub dec ex (honestOverlay tg pub)) j := by
    intro j
    have h1 : ¬ (13 + (j : ℕ) < 13) := by omega
    have h2 : 13 + (j : ℕ) < 76 := by omega
    simp only [E, honestSrcEnv, CorrectedFinalTypedEnv.toSourceEnv, h1, h2, dif_neg, dif_pos,
      not_false_eq_true]
    have hj : 13 + (j : ℕ) - 13 = j := by omega
    by_cases h54 : (j : ℕ) = 54
    · simp only [hj, h54, if_true]
      have : j = 54 := Fin.ext h54
      subst this
      simp [coreExtensionValue, row309, sampledEncode309, sampledEncodeExtension309,
        sampledEncodeExtension, OptimizedComputeCodec.encodeExtension]
    by_cases h55 : (j : ℕ) = 55
    · simp only [hj, h55, if_true]
      have : j = 55 := Fin.ext h55
      subst this
      simp [coreExtensionValue, row309, sampledEncode309, sampledEncodeExtension309,
        sampledEncodeExtension, OptimizedComputeCodec.encodeExtension]
    simp only [hj, h54, h55, if_false]
    have hr := towerEnv309_ext_of_src b v eF hF ⟨j, by omega⟩
      (genRowVals_imZero pub dec ex i n wc wa wln winv r58 r59 vcl tg h58 h61 h62 ⟨j, by omega⟩ h54 h55)
    rw [hr]
    exact genRowVals_ext_lt pub dec ex i n wc wa wln winv r58 r59 vcl tg j j.isLt
  have hc0 : E.toSourceEnv.chal 0 = inp.α := by
    simp [E, honestSrcEnv, CorrectedFinalTypedEnv.toSourceEnv, inp, towerInputs]
  have hc5 : E.toSourceEnv.chal 5 = inp.z⁻¹ := by
    have := hchal.2.2.2.2.1
    simp only [E, honestSrcEnv, CorrectedFinalTypedEnv.toSourceEnv, show (5 : ℕ) < 12 by norm_num,
      dif_pos]
    simpa [inp, towerInputs] using this
  have hR : Row309Reads (F := F) E.toSourceEnv inp pub dec ex (honestOverlay tg pub) :=
    ⟨hsel, hext, hc0, hc5⟩
  refine ⟨⟨hR.table hv, ?_, ?_, honestEx_air wf hv hz, hsel⟩, agreeOffT_honestSrc T αs _ _⟩
  · intro j hj
    obtain ⟨h1, h2, h3, h4, -⟩ := hchal
    interval_cases j <;>
      simp [Env.ofSubst, computeSubst, Expr.eval, computeEnvFull, E, honestSrcEnv,
        CorrectedFinalTypedEnv.toSourceEnv, inp, towerInputs] <;>
      first | exact h1 | exact h2 | exact h3 | exact h4
  · intro j
    rw [honestSrcEnv_pub]
    rfl

end Match

/-! ## 5. `V_comp` and `WF` at every generated BFS row -/

section GenRows
open Nock.NockVMROM.Thm54.TraceGen Nock.Walk Nock.TableWFBounds

variable {L : Type} [Field L]

theorem renderNode_inputs (z α : L) (g : GenComputeRow L) :
    (renderNode z α g).row.2.1 = ⟨α, z, 0, 0, 0⟩ := by
  unfold renderNode
  split <;> rfl

/-- **`V_comp` and `WF` at every BFS row of the AIR-ordered generated tree, at the re-keyed coins.**
`SeedGood` (the bad-seed census) and the per-row OP5 condition `rlc5Holds a b c` (a named honestBad
event) are the only coin hypotheses. -/
theorem gen_vcomp_wf (z αs a b c : L) (hz : z ≠ 0) {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow L)} {result : Noun}
    (h : genComputeSkeleton (K := L) fuel subject formula = .ok (t, result))
    (hgood : SeedGood z t) {i : ℕ} (hi : i ∈ List.range' 1 (bfsForest [airReorder t]).length)
    (h5 : rlc5Holds a b c (renderNode z αs (bfsLabelAt (airReorder t) i)).row.2.2.1) :
    Vcomp ⟨αs, z, a, b, c⟩ (renderNode z αs (bfsLabelAt (airReorder t) i)).row.2.2.1
        (renderNode z αs (bfsLabelAt (airReorder t) i)).row.2.2.2 ∧
      WF ⟨αs, z, a, b, c⟩ (renderNode z αs (bfsLabelAt (airReorder t) i)).row.2.2.1 := by
  have hv := genComputeSkeleton_airReorder_bfsLabelAt_Vcomp_of_seedGood z αs hz h hgood hi
  rw [renderNode_inputs] at hv
  refine ⟨(Vcomp_abc_irrel ⟨αs, z, 0, 0, 0⟩ a b c _ _).mpr hv, ?_⟩
  exact renderNode_WF z αs a b c _ hz h5

end GenRows

/-! ## 6. C1b's base-cell and bank hypotheses from the row index and the end states -/

section Cells
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **`HonestBaseCells` at every honest row** (feeds `base15_of_cells` / `eq22_of_cells`). -/
theorem genRow_baseCells (b : Basis (Fin 3) F K)
    (pub : Pub (Quad (algebraMap F K δ))) (dec : Dec (Quad (algebraMap F K δ)))
    (ex : Extra (Quad (algebraMap F K δ))) (i n : ℕ)
    (wc wa wln winv r58 r59 : Quad (algebraMap F K δ)) (vcl : ℕ → F) (tg : Fin 3 → Quad (algebraMap F K δ)) (E : Env F)
    (hF : ∀ c, SrcRead c → E.trace c = srcColT b
      (genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg) c) :
    HonestBaseCells n i (stateIndex pub.state) E :=
  honestBaseCells_of_src b _ E hF n i _
    (fun j hj => by simp [genRowVals, hj])
    (by simp [genRowVals]) (by simp [genRowVals])

/-- **The `eq22_of_cells` side conditions** for a family of rows `pubAt`: with `s0`/`sL` the state
indices of rows `0` and `n − 1`, row `i` meets `h0` and `hL` by construction; the banks are the
package publics `x` read through `pubCFT_bank`. -/
theorem genRow_eq_hyps (pubAt : ℕ → Pub (Quad (algebraMap F K δ))) (n i : ℕ) :
    (i = 0 → (stateIndex (pubAt i).state : ℕ) = stateIndex (pubAt 0).state) ∧
      (i + 1 = n → (stateIndex (pubAt i).state : ℕ) = stateIndex (pubAt (n - 1)).state) :=
  ⟨fun h => by subst h; rfl, fun h => by rw [show i = n - 1 by omega]⟩

/-- The selector banks of `pubCFT` at package publics that are the one-hots of the end states. -/
theorem genRow_banks (χ : Coins frameVCL K) {hC : ℕ} {S : MemShape} (V : VerifierData F K hC S)
    (x : ℕ → F) (ρ : Fin 3 → Quad (algebraMap F K δ)) (E : Env F) (hp : E.pub = pubCFT δ V x ρ χ)
    (s0 sL : ℕ) (hx0 : ∀ j, j < 11 → x (20 + j) = if j = s0 then 1 else 0)
    (hxL : ∀ j, j < 11 → x (31 + j) = if j = sL then 1 else 0) :
    (∀ j, j < 11 → E.pub (20 + j) = if j = s0 then 1 else 0) ∧
      (∀ j, j < 11 → E.pub (31 + j) = if j = sL then 1 else 0) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rw [hp, pubCFT_bank δ χ V x ρ _ (Or.inr (by omega)), hx0 j hj]
  · rw [hp, pubCFT_bank δ χ V x ρ _ (Or.inr (by omega)), hxL j hj]

end Cells

/-! ## 7. The walk interface (C2b `WalkGatesT.WalkRowEnv`): the fields the fill supplies -/

section Walk
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **The current-row walk fields of C2b's `WalkRowEnv`** read back from the honest fill:
`W0/W1`, roles `58/59/61/62`, masks `11/12`.  Instantiate `wc wa wln winv` at `D.cnt (i+1)`,
`D.acc (i+1)`, `D.ln (i+1)`, `(D.cnt (i+1) − D.ln (i+1))⁻¹` and `r58 r59` at the residual values.
Hypotheses: `W0`, role `58`, `61`, `62` are `𝕂`-valued (no Im column). -/
theorem genRow_walkFields (b : Basis (Fin 3) F K)
    (pub : Pub (Quad (algebraMap F K δ))) (dec : Dec (Quad (algebraMap F K δ)))
    (ex : Extra (Quad (algebraMap F K δ))) (i n : ℕ)
    (wc wa wln winv r58 r59 : Quad (algebraMap F K δ)) (vcl : ℕ → F) (tg : Fin 3 → Quad (algebraMap F K δ)) (eF : Env F)
    (hF : ∀ c, SrcRead c → eF.trace c = srcColT b
      (genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg) c)
    (hwc : Quad.im _ wc = 0) (h58 : Quad.im _ r58 = 0) (h61 : Quad.im _ wln = 0)
    (h62 : Quad.im _ winv = 0) :
    (towerEnv309 δ towerM (gatherEnv b eF) eF).walk 0 = wc ∧
    (towerEnv309 δ towerM (gatherEnv b eF) eF).walk 1 = wa ∧
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.extTrace 58 = r58 ∧
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.extTrace 59 = r59 ∧
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.extTrace 61 = wln ∧
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.extTrace 62 = winv ∧
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.baseTrace 11 = (if i = 0 then 1 else 0) ∧
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.baseTrace 12 = (if i + 1 = n then 1 else 0) := by
  set v := genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg
  have hW0 : Quad.im _ (v.walk 0) = 0 := by simpa [v, genRowVals] using hwc
  have hr : ∀ r : Fin 63, r.val ≠ 54 → r.val ≠ 55 →
      (towerEnv309 δ towerM (gatherEnv b eF) eF).base.extTrace r = v.ext r := fun r h54 h55 =>
    towerEnv309_ext_of_src b v eF hF r
      (genRowVals_imZero pub dec ex i n wc wa wln winv r58 r59 vcl tg h58 h61 h62 r h54 h55)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [towerEnv309_walk_of_src b v eF hF hW0 0]; simp [v, genRowVals]
  · rw [towerEnv309_walk_of_src b v eF hF hW0 1]; simp [v, genRowVals]
  · rw [hr 58 (by decide) (by decide)]; simp [v, genRowVals]
  · rw [hr 59 (by decide) (by decide)]; simp [v, genRowVals]
  · rw [hr 61 (by decide) (by decide)]; simp [v, genRowVals]
  · rw [hr 62 (by decide) (by decide)]; simp [v, genRowVals]
  · rw [towerEnv309_base_of_src b v eF hF 11]; simp [v, genRowVals]
  · rw [towerEnv309_base_of_src b v eF hF 12]; simp [v, genRowVals]

/-- **The successor-row walk fields** (`WalkRowEnv.nxt`, value part): with `hFn` the next-row
placement of row `i+1`'s fill, `W0/W1` and role `61` of the next row read back. -/
theorem genRow_walkNextFields (b : Basis (Fin 3) F K)
    (pub : Pub (Quad (algebraMap F K δ))) (dec : Dec (Quad (algebraMap F K δ)))
    (ex : Extra (Quad (algebraMap F K δ))) (i n : ℕ)
    (wc wa wln winv r58 r59 : Quad (algebraMap F K δ)) (vcl : ℕ → F) (tg : Fin 3 → Quad (algebraMap F K δ)) (eF : Env F)
    (hFn : ∀ c, SrcRead c → eF.traceNext c = srcColT b
      (genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg) c)
    (hwc : Quad.im _ wc = 0) (h61 : Quad.im _ wln = 0) :
    (towerEnv309 δ towerM (gatherEnv b eF) eF).walkNext 0 = wc ∧
    (towerEnv309 δ towerM (gatherEnv b eF) eF).walkNext 1 = wa ∧
    (towerEnv309 δ towerM (gatherEnv b eF) eF).base.extTraceNext 61 = wln := by
  set v := genRowVals pub dec ex i n wc wa wln winv r58 r59 vcl tg
  have hW0 : Quad.im _ (v.walk 0) = 0 := by simpa [v, genRowVals] using hwc
  refine ⟨?_, ?_, ?_⟩
  · rw [towerEnv309_walkNext_of_src b v eF hFn hW0 0]; simp [v, genRowVals]
  · rw [towerEnv309_walkNext_of_src b v eF hFn hW0 1]; simp [v, genRowVals]
  · rw [towerEnv309_extNext_of_src b v eF hFn 61 (fun _ => by simpa [v, genRowVals] using h61)]
    simp [v, genRowVals]

end Walk

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
