import Nock.NockVMROM.Thm54.VclL.Compute.Gates
import Nock.NockVMROM.Thm54.VclL.Compute.Support
import Nock.NockVMROM.Thm54.P8Core.RepartitionedStaging

/-!
# V4 (b), part 2: `computeChipVCL`, the reindex-and-filter of `allGates309`

`computeChipVCL` is `ProductionNamedComputeRAP309` with

* Form R deleted: the 97 `formRCertificateGates`, the 6 `formRLamPins` coordinates and the two core
  gates that read Form R (ids `79`, `80`, the record-1/2 denominator pins) are filtered out;
  base columns `202..301` are removed;
* the carrier `S` (`302`) kept as the row serial at arity 1 (`serialGates`, `Gates.lean`), moved to
  the TAIL column `220 = w − 1` (round `0` by `colRoundVCL`, as `layoutVCL`'s stub assumes);
* the walk columns `W0/W1` (`303..308`) moved to `208..213`;
* the **new round-0 B0 columns** `vIdx₀, vIdx₁` (`202, 203`) and the two root bindings' `idx`/`μ`
  (`204..207`), and the round-1 lookup inverses (`214..219`, two triples).  They are columns of the
  layout (`colRoundVCL`); the gates that pin them to the reshaped records are the part-(c) twins.

Layout (`𝕂`, `e = 3`): `w = 221` (`wRAP = ![208, 13]`: the `wRAP` split is a physical RAP prefix; the
coin-round schedule is `colRoundVCL`, decoupled from it exactly as at 309, where `S = 302` sits past
the round-1 block yet is round `0`).  The ln/`ln_prev` columns are RETAINED (their gates are
untouched); with them the width is `309 − 100 + 12 = 221`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock Nock.Framework Nock.Reified Module
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedComputeFinal Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering hiding finalExtCoordIndex
open Nock.NockVMROM.Thm54.MonolithicRAP
open scoped Polynomial

set_option maxRecDepth 300000

noncomputable section

/-! ## 1. The column map and the layout -/

/-- Old physical column (outside `[202, 302)`) to the new one: below `202` fixed; `S` `302 ↦ 220` (tail);
the walk columns `303..308 ↦ 208..213`. -/
def vclCol (i : ℕ) : ℕ := if i < 202 then i else if i = 302 then serialCol else i - 95

theorem vclCol_walk (i : ℕ) (h : 303 ≤ i) : vclCol i = i - 95 := by
  simp only [vclCol]; split_ifs <;> omega

/-- The new column groups. -/
def vIdxCol (j : Fin 2) : ℕ := 202 + (j : ℕ)
def rootCol (j : Fin 4) : ℕ := 204 + (j : ℕ)
def walkColVCL (j : Fin 2) (k : Fin 3) : ℕ := 208 + 3 * (j : ℕ) + (k : ℕ)
def lookupInvBase (j : Fin 2) : ℕ := 214 + 3 * (j : ℕ)

def vclWidth : ℕ := 221
def vclRound0 : ℕ := 208

/-- The coin-round schedule of `computeChipVCL` (the 309 schedule `newComputeColRound` on the kept
columns; the new B0 columns and the serial are round `0`, the lookup inverses round `1`, the walk
columns round `2`). -/
def colRoundVCL (c : ℕ) : ℕ :=
  if c < 202 then RepartitionedStaging.newComputeColRound c
  else if c < 208 then 0 else if c < 214 then 2 else if c < 220 then 1 else 0

theorem colRoundVCL_serial : colRoundVCL serialCol = 0 := by decide
theorem colRoundVCL_walk (j : Fin 2) (k : Fin 3) :
    colRoundVCL (walkColVCL j k) = RepartitionedStaging.newComputeColRound (walkLimb j k) := by
  fin_cases j <;> fin_cases k <;> decide
theorem colRoundVCL_vIdx (j : Fin 2) : colRoundVCL (vIdxCol j) = 0 := by fin_cases j <;> decide

theorem vclCol_walkLimb (j : Fin 2) (k : Fin 3) : vclCol (walkLimb j k) = walkColVCL j k := by
  have := j.isLt; have := k.isLt
  rw [vclCol_walk _ (by simp only [walkLimb]; omega)]
  simp only [walkLimb, walkColVCL]; omega

theorem vclCol_lt (i : ℕ) (h : i < 309) (hn : NoFormR i) : vclCol i < 221 := by
  simp only [NoFormR] at hn; simp only [vclCol, serialCol]; (repeat' split) <;> omega

theorem vclCol_inj {i j : ℕ} (hi : NoFormR i) (hj : NoFormR j) (hi' : i < 309) (hj' : j < 309)
    (h : vclCol i = vclCol j) : i = j := by
  simp only [NoFormR] at hi hj; simp only [vclCol, serialCol] at h; split_ifs at h <;> omega

/-- Reindex the trace columns of an expression. -/
def reindexE {F : Type*} : CoeffExpr F → CoeffExpr F
  | .const c => .const c
  | .var .traceCur i => .var .traceCur (vclCol i)
  | .var .traceNext i => .var .traceNext (vclCol i)
  | .var k i => .var k i
  | .add a b => .add (reindexE a) (reindexE b)
  | .sub a b => .sub (reindexE a) (reindexE b)
  | .mul a b => .mul (reindexE a) (reindexE b)
  | .neg a => .neg (reindexE a)
  | .pow a n => .pow (reindexE a) n

theorem degree_reindexE {F : Type*} (e : CoeffExpr F) : (reindexE e).degree = e.degree := by
  induction e with
  | const c => rfl
  | var k i => cases k <;> rfl
  | add a b ha hb => simp [reindexE, CoeffExpr.degree, ha, hb]
  | sub a b ha hb => simp [reindexE, CoeffExpr.degree, ha, hb]
  | mul a b ha hb => simp [reindexE, CoeffExpr.degree, ha, hb]
  | neg a ha => simp [reindexE, CoeffExpr.degree, ha]
  | pow a n ha => simp [reindexE, CoeffExpr.degree, ha]

/-- **The reindex bridge** (what part (c) consumes): an expression free of `[202, 302)` evaluates
after reindexing, at an environment whose trace is the old trace transported along `vclCol`, to
its old value. -/
theorem eval_reindexE {F : Type*} [Field F] (e : CoeffExpr F) (env env' : Env F)
    (hcols : ColsIn NoFormR e)
    (hc : ∀ i, NoFormR i → env'.trace (vclCol i) = env.trace i)
    (hn : ∀ i, NoFormR i → env'.traceNext (vclCol i) = env.traceNext i)
    (hch : env'.chal = env.chal) (hp : env'.pub = env.pub) :
    (reindexE e).eval env' = e.eval env := by
  induction e with
  | const c => rfl
  | var k i =>
      cases k
      · exact hc i (hcols i (by simp [colsOf]))
      · exact hn i (hcols i (by simp [colsOf]))
      · simp [reindexE, CoeffExpr.eval, hch]
      · simp [reindexE, CoeffExpr.eval, hp]
  | add a b ha hb =>
      simp only [reindexE, CoeffExpr.eval]
      rw [ha (fun i hi => hcols i (by simp [colsOf, hi])), hb (fun i hi => hcols i (by simp [colsOf, hi]))]
  | sub a b ha hb =>
      simp only [reindexE, CoeffExpr.eval]
      rw [ha (fun i hi => hcols i (by simp [colsOf, hi])), hb (fun i hi => hcols i (by simp [colsOf, hi]))]
  | mul a b ha hb =>
      simp only [reindexE, CoeffExpr.eval]
      rw [ha (fun i hi => hcols i (by simp [colsOf, hi])), hb (fun i hi => hcols i (by simp [colsOf, hi]))]
  | neg a ha =>
      simp only [reindexE, CoeffExpr.eval]
      rw [ha hcols]
  | pow a n ha =>
      simp only [reindexE, CoeffExpr.eval]
      rw [ha hcols]

/-! ## 2. The gate list -/

section gates
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The kept `allGates309` groups, before the reindex. -/
def keptGates309 (n : ℕ) (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  finalBaseTransitionGates n ++ correctedCoreVCL b ++ correctedAux309 b ++
    compileList309 b endpoint2_309 ++ compileList309 b endpoint4_309 ++ finalEndpointEqualityChecks

/-- **The gates of `computeChipVCL`**: the kept groups reindexed, then the arity-1 serial. -/
def vclGates (n : ℕ) (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  (keptGates309 n b).map reindexE ++ serialGates

theorem keptGates309_colsIn (n : ℕ) (b : Basis (Fin 3) F K) :
    ∀ g ∈ keptGates309 n b, ColsIn NoFormR g := by
  intro g hg
  simp only [keptGates309, List.mem_append] at hg
  rcases hg with ((((hb | hc) | ha) | h2) | h4) | heq
  · exact finalBaseTransitionGates_colsIn n g hb
  · exact correctedCoreVCL_colsIn b g hc
  · exact correctedAux309_colsIn b g ha
  · exact compileList309_colsIn b _ endpoint2_noCert g h2
  · exact compileList309_colsIn b _ endpoint4_noCert g h4
  · exact finalEndpointEqualityChecks_colsIn g heq

theorem keptGates309_length (n : ℕ) (b : Basis (Fin 3) F K) : (keptGates309 n b).length = 307 := by
  simp only [keptGates309, List.length_append, finalBaseTransitionGates_length,
    correctedCoreVCL_length, correctedAux309_length, compileList309_length,
    finalEndpointEqualityChecks_length]
  have h := endpoint_lengths309
  omega

theorem vclGates_length (n : ℕ) (b : Basis (Fin 3) F K) : (vclGates n b).length = 309 := by
  simp [vclGates, keptGates309_length]

theorem keptGates309_degree (n : ℕ) (b : Basis (Fin 3) F K) : ∀ g ∈ keptGates309 n b, g.degree ≤ 4 := by
  intro g hg
  simp only [keptGates309, List.mem_append] at hg
  rcases hg with ((((hb | hc) | ha) | h2) | h4) | heq
  · exact (finalBaseTransitionGates_degree n g hb).trans (by decide)
  · simp only [correctedCoreVCL, List.mem_flatten, List.mem_map] at hc
    obtain ⟨_, ⟨i, _, rfl⟩, hc⟩ := hc
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hc
    exact correctedCoreCoord309_degree b i k
  · rw [correctedAux309] at ha
    obtain ⟨xs, hxs, ha⟩ := List.mem_flatten.mp ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hxs
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
    exact correctedAuxCoord309_degree b j k
  · exact (compileList309_degree b endpoint2_309 2 endpoint2_309_degree g h2).trans (by decide)
  · exact compileList309_degree b endpoint4_309 4 endpoint4_309_degree g h4
  · exact (finalEndpointEqualityChecks_degree g heq).trans (by decide)

theorem vclGates_degree (n : ℕ) (b : Basis (Fin 3) F K) : ∀ g ∈ vclGates n b, g.degree ≤ 4 := by
  intro g hg
  simp only [vclGates, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨g', hg', rfl⟩ | hs
  · rw [degree_reindexE]; exact keptGates309_degree n b g' hg'
  · exact (serialGates_degree g hs).trans (by decide)

end gates

/-! ## 3. The RAP and the chip -/

def vclRAP {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) : RAP F :=
  { e := 3
    k := 2
    wRAP := ![vclRound0, 13]
    w := vclWidth
    w_eq := by simp [Fin.sum_univ_two, vclRound0, vclWidth]
    h := h
    d := 4
    s := (vclGates n b).length
    ω := orbit.ω
    β := orbit.βcoset
    I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
    C := fun i => coeffToMv chalVal pubVal ((vclGates n b).get i)
    C_vars := fun _i => coeffToMv_vars chalVal pubVal _
    C_deg := fun _i => (coeffToMv_totalDegree_le chalVal pubVal _).trans
      (vclGates_degree n b _ (List.get_mem _ _))
    H := H
    β_ne_zero := orbit.βcoset_ne_zero
    I_bound := by
      intro q hq
      have hq2 : q.2 = 0 ∨ q.2 = 1 := by
        have h2 := (Finset.mem_product.mp hq).2
        simpa [Finset.mem_insert, Finset.mem_singleton] using h2
      have hge : 2 ≤ 2 ^ h := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) orbit.h_pos
      rcases hq2 with hq' | hq' <;> rw [hq'] <;> omega }

/-- **`computeChipVCL`**: the compute chip of VCL-L, beside `ProductionNamedComputeRAP309`. -/
def computeChipVCL
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) : FixedPreprocessingRAP F where
  rap := vclRAP (n := n) b chalVal pubVal orbit (rowNodeSet nodes)
  rounds_pos := by norm_num [vclRAP]
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨11 + (j : ℕ), by
          have := j.isLt
          change 11 + (j : ℕ) < vclRound0
          simp only [vclRound0]
          omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

/-- **Acceptance at `computeChipVCL` is the bound preprocessing plus every gate of `vclGates` at
every row environment** (the analogue of `satisfies309_iff_sourceLanguage` at the gate level; the
typed `VclSourceObligations` reading of this list is part (c)). -/
theorem computeChipVCL_sat_iff
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCL hn nodes b chalVal pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing (computeChipVCL hn nodes b chalVal pubVal orbit) P ↔
      (computeChipVCL hn nodes b chalVal pubVal orbit).BindsPreprocessing P ∧
        ∀ x ∈ rowNodeSet nodes, ∀ g ∈ vclGates n b,
          g.eval (Reify.envOfTrace P orbit.ω x chalVal pubVal) = 0 := by
  have key : ∀ (i : Fin (computeChipVCL hn nodes b chalVal pubVal orbit).rap.s) (x : F),
      ((computeChipVCL hn nodes b chalVal pubVal orbit).rap.compose P i).eval x =
        ((vclGates n b).get i).eval (Reify.envOfTrace P orbit.ω x chalVal pubVal) := by
    intro i x
    rw [Reify.compose_eval]
    exact eval_coeffToMv P orbit.ω x chalVal pubVal _
  constructor
  · rintro ⟨hraw, hfixed⟩
    refine ⟨hfixed, fun x hx g hg => ?_⟩
    obtain ⟨i, hget⟩ := List.mem_iff_get.mp hg
    have hz := hraw i x hx
    rw [key i x] at hz
    rwa [← hget]
  · rintro ⟨hfixed, hall⟩
    refine ⟨?_, hfixed⟩
    intro i x hx
    rw [key i x]
    exact hall x hx _ (List.get_mem _ _)

/-- **The measured fingerprint** `(e, w, s, d, k) = (3, 221, 309, 4, 2)` over `𝕂` (no tower). -/
theorem vclRAP_fingerprint
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    let R := vclRAP (n := n) b chalVal pubVal orbit H
    R.w = 221 ∧ R.s = 309 ∧ R.d = 4 ∧ R.k = 2 ∧ R.e = 3 ∧ R.wRAP = ![208, 13] :=
  ⟨rfl, vclGates_length n b, rfl, rfl, rfl, rfl⟩

end

end VclL.Compute
end Nock.NockVMROM.Thm54
