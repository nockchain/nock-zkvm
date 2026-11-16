import Nock.NockVMROM.Thm54.VclL.Compute.Keys
import Nock.NockVMROM.Thm54.StrategyOfTracesLift

/-!
# The round-0 axis column `ax`

* **The column.** `ax` is base column `221` (round `0`: `colRoundVCL_ax`); the repaired chip is
  `221 + 1 = 222` columns wide, the serial stays at `220`.
* `f_t.leaf` / `f_th.leaf` are the `𝕂`-roles `41` / `44` (physical limbs
  `136..138` / `145..147`), state-independently: `decodeDec_ft_leaf` / `decodeDec_fth_leaf` read the
  deployed decoder (`StrategyOfTracesLift.decodeDec`, the source columns `52` / `55`).
* **(i) honest `ax` is coin-free** (`honestAx`, `honest_axGates`): a function of the compute skeleton
  row (`state`, `formula`) only; at the honest row the gate holds at EVERY seed `z`, because the
  NPR fingerprint of an atom has leaf coordinate the atom itself (`GlobalCarryRecognizer.enc_atom`).
* **(ii) the gate binds the key to the join's leaf** (`axGate_ax0`, `axGate_ax9`): on any row where
  the three gates vanish, an `s0` row has `natLift ax = n` whenever the decoded `f_t.leaf = (n : K)`
  with `n < ringChar F` — exactly `Batch1171.RowFacts.ax0`'s clause with `ax (S + 2) := natLift ax` —
  and `natLift ax < ringChar F` (`natLift_lt`); same at `s9` with `f_th.leaf`.
* **The repaired chip** `computeChipVCLA` (`vclGatesA = vclGates ++ axGates`, `(e, w, s, d, k) =
  (3, 222, 312, 4, 2)`, `computeChipVCLA_sat_iff`) and **the path key at B0** (`path_key_clause`:
  the path record `(fp root, fp child, ax, vIdx)`'s key `(natLift slot 7, natLift slot 6)` is the
  `B0Cols`-typed `recKeyPath` reading columns `vIdxCol j` and `221`).

Paper: `:1742` (OP0's record `⟨s, e, f_t.leaf⟩`), `:1737-1738` (OP9's `⟨sf1_e, sf2_f, f_th.leaf⟩`),
`:1751` (OP0's formula tail as the NMR address), `:1456-1479` (rounds).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock Nock.Framework Nock.Reified Module
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.RecordCarrier
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering hiding finalExtCoordIndex
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.MonolithicRAP
open scoped Polynomial

set_option maxRecDepth 300000

noncomputable section

/-! ## 1. The column and the gate -/

/-- The axis column: base column `221`, the new tail of the repaired chip. -/
def axCol : ℕ := 221

def vclWidthA : ℕ := 222

theorem colRoundVCL_ax : colRoundVCL axCol = 0 := by decide

/-- The physical limb of coordinate `k` of `f_t.leaf` (`𝕂`-role `41`). -/
def ftLeafLimb (k : Fin 3) : ℕ := 136 + (k : ℕ)
/-- The physical limb of coordinate `k` of `f_th.leaf` (`𝕂`-role `44`). -/
def fthLeafLimb (k : Fin 3) : ℕ := 145 + (k : ℕ)

section gate
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- Coordinate `k` of `s0·(f_t.leaf − ax) + s9·(f_th.leaf − ax)` (`ax ∈ 𝔽` embedded in `𝕂`: its
coordinate `k` is `ax · coord 1 k`). -/
def axGateCoord (b : Basis (Fin 3) F K) (k : Fin 3) : CoeffExpr F :=
  .add
    (.mul (.var .traceCur 0)
      (.sub (.var .traceCur (ftLeafLimb k)) (.mul (.var .traceCur axCol) (.const (coord b 1 k)))))
    (.mul (.var .traceCur 9)
      (.sub (.var .traceCur (fthLeafLimb k)) (.mul (.var .traceCur axCol) (.const (coord b 1 k)))))

def axGates (b : Basis (Fin 3) F K) : List (CoeffExpr F) := List.ofFn (axGateCoord b)

@[simp] theorem axGates_length (b : Basis (Fin 3) F K) : (axGates b).length = 3 := by
  simp [axGates]

theorem axGates_degree (b : Basis (Fin 3) F K) : ∀ g ∈ axGates b, g.degree ≤ 2 := by
  intro g hg
  simp only [axGates, List.mem_ofFn] at hg
  obtain ⟨k, rfl⟩ := hg
  simp [axGateCoord, CoeffExpr.degree]

theorem axGateCoord_eval (b : Basis (Fin 3) F K) (k : Fin 3) (env : Env F) :
    (axGateCoord b k).eval env =
      env.trace 0 * (env.trace (ftLeafLimb k) - env.trace axCol * coord b 1 k) +
        env.trace 9 * (env.trace (fthLeafLimb k) - env.trace axCol * coord b 1 k) := rfl

end gate

/-! ## 2. The decoder reads roles `41` / `44` -/

section decode
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The deployed decoder's `f_t.leaf` is the `𝕂`-role `41` (source column `52`, state-independent). -/
theorem decodeDec_ft_leaf (env : CorrectedFinalTypedEnv F K) :
    (StrategyOfTracesLift.decodeDec env).f_t.leaf = env.extTrace ⟨41, by omega⟩ := rfl

/-- The deployed decoder's `f_th.leaf` is the `𝕂`-role `44` (source column `55`). -/
theorem decodeDec_fth_leaf (env : CorrectedFinalTypedEnv F K) :
    (StrategyOfTracesLift.decodeDec env).f_th.leaf = env.extTrace ⟨44, by omega⟩ := rfl

theorem gather_ext41 [FiniteDimensional F K] (b : Basis (Fin 3) F K) (envF : Env F) :
    (gatherCorrectedFinalTypedEnv b envF).extTrace ⟨41, by omega⟩ =
      ∑ k : Fin 3, envF.trace (ftLeafLimb k) • b k := rfl

theorem gather_ext44 [FiniteDimensional F K] (b : Basis (Fin 3) F K) (envF : Env F) :
    (gatherCorrectedFinalTypedEnv b envF).extTrace ⟨44, by omega⟩ =
      ∑ k : Fin 3, envF.trace (fthLeafLimb k) • b k := rfl

/-- A coordinate vector `a · coord 1` reassembles to `algebraMap a`. -/
theorem sum_coord_one_smul [FiniteDimensional F K] (b : Basis (Fin 3) F K) (a : F) :
    ∑ k : Fin 3, (a * coord b 1 k) • b k = algebraMap F K a := by
  have h1 : ∑ k : Fin 3, coord b (1 : K) k • b k = 1 := b.sum_repr 1
  calc ∑ k : Fin 3, (a * coord b 1 k) • b k = a • ∑ k : Fin 3, coord b (1 : K) k • b k := by
        rw [Finset.smul_sum]; simp [mul_smul]
    _ = algebraMap F K a := by rw [h1, Algebra.algebraMap_eq_smul_one]

end decode

/-! ## 3. (ii): the gate forces the key's axis to be the join's leaf -/

section sound
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- `natLift` is below the characteristic when the characteristic is positive. -/
theorem natLift_lt (hF : 0 < ringChar F) (x : F) : natLift x < ringChar F := by
  classical
  unfold natLift
  split
  · rename_i h; exact (Nat.find_spec h).1
  · exact hF

/-- `algebraMap a = (n : K)` with `n < ringChar F` gives `natLift a = n`. -/
theorem natLift_of_algebraMap {a : F} {n : ℕ} (hn : n < ringChar F)
    (h : algebraMap F K a = (n : K)) : natLift a = n := by
  have ha : a = (n : F) := by
    apply (algebraMap F K).injective
    rw [h, map_natCast]
  rw [ha, natLift_natCast hn]

theorem axGates_s0 (b : Basis (Fin 3) F K) (envF : Env F)
    (hg : ∀ g ∈ axGates b, g.eval envF = 0) (h0 : envF.trace 0 = 1) (h9 : envF.trace 9 = 0) :
    (gatherCorrectedFinalTypedEnv b envF).extTrace ⟨41, by omega⟩ = algebraMap F K (envF.trace axCol) := by
  have hk : ∀ k : Fin 3, envF.trace (ftLeafLimb k) = envF.trace axCol * coord b 1 k := by
    intro k
    have := hg (axGateCoord b k) (List.mem_ofFn.2 ⟨k, rfl⟩)
    rw [axGateCoord_eval, h0, h9] at this
    linear_combination this
  rw [gather_ext41, ← sum_coord_one_smul b]
  exact Finset.sum_congr rfl fun k _ => by rw [hk k]

theorem axGates_s9 (b : Basis (Fin 3) F K) (envF : Env F)
    (hg : ∀ g ∈ axGates b, g.eval envF = 0) (h0 : envF.trace 0 = 0) (h9 : envF.trace 9 = 1) :
    (gatherCorrectedFinalTypedEnv b envF).extTrace ⟨44, by omega⟩ = algebraMap F K (envF.trace axCol) := by
  have hk : ∀ k : Fin 3, envF.trace (fthLeafLimb k) = envF.trace axCol * coord b 1 k := by
    intro k
    have := hg (axGateCoord b k) (List.mem_ofFn.2 ⟨k, rfl⟩)
    rw [axGateCoord_eval, h0, h9] at this
    linear_combination this
  rw [gather_ext44, ← sum_coord_one_smul b]
  exact Finset.sum_congr rfl fun k _ => by rw [hk k]

/-- **(ii) at OP0**: on a row where the axis gates vanish and the state is `s0`, the B0 key axis
`natLift ax` is the atom the C2 join reads off the decoded `f_t.leaf` (`RowFacts.ax0`'s clause). -/
theorem axGate_ax0 (b : Basis (Fin 3) F K) (envF : Env F)
    (hg : ∀ g ∈ axGates b, g.eval envF = 0) (h0 : envF.trace 0 = 1) (h9 : envF.trace 9 = 0) :
    ∀ n : ℕ, n < ringChar F →
      (StrategyOfTracesLift.decodeDec (gatherCorrectedFinalTypedEnv b envF)).f_t.leaf = (n : K) →
      natLift (envF.trace axCol) = n := by
  intro n hn hleaf
  rw [decodeDec_ft_leaf, axGates_s0 b envF hg h0 h9] at hleaf
  exact natLift_of_algebraMap hn hleaf

/-- **(ii) at OP9**: the same with `f_th.leaf`. -/
theorem axGate_ax9 (b : Basis (Fin 3) F K) (envF : Env F)
    (hg : ∀ g ∈ axGates b, g.eval envF = 0) (h0 : envF.trace 0 = 0) (h9 : envF.trace 9 = 1) :
    ∀ n : ℕ, n < ringChar F →
      (StrategyOfTracesLift.decodeDec (gatherCorrectedFinalTypedEnv b envF)).f_th.leaf = (n : K) →
      natLift (envF.trace axCol) = n := by
  intro n hn hleaf
  rw [decodeDec_fth_leaf, axGates_s9 b envF hg h0 h9] at hleaf
  exact natLift_of_algebraMap hn hleaf

end sound

/-! ## 4. (i): honest `ax` is coin-free -/

/-- **The honest axis column**, a function of the skeleton row alone: OP0 `[0 b]` → `b`, OP9
`[9 b c]` → `b`, every other state `0`. -/
def honestAx (v : SemanticStrategy.ComputeRowSkeleton) : ℕ :=
  match v.state, v.formula with
  | .s0, .cell _ (.atom b) => b
  | .s9, .cell _ (.cell (.atom b) _) => b
  | _, _ => 0

section honest
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- The NPR fingerprint of an atom has leaf coordinate the atom, at every seed. -/
theorem enc_atom_leaf (z : K) (a : ℕ) : (GlobalCarryRecognizer.enc z (.atom a)).leaf = (a : K) := by
  rw [GlobalCarryRecognizer.enc_atom]; rfl

/-- **(i)**: at a row whose leaf limbs carry the coordinates of the honest fingerprints at ANY seed
`z` of atoms `a₀` (OP0 tail) / `a₉` (OP9 tail head), the axis gates hold with `ax = (a : F)` for the
active state's atom — `z` does not enter. -/
theorem honest_axGates (b : Basis (Fin 3) F K) (z : K) (a₀ a₉ : ℕ) (envF : Env F)
    (hsel : (envF.trace 0 = 1 ∧ envF.trace 9 = 0 ∧ envF.trace axCol = (a₀ : F)) ∨
      (envF.trace 0 = 0 ∧ envF.trace 9 = 1 ∧ envF.trace axCol = (a₉ : F)) ∨
      (envF.trace 0 = 0 ∧ envF.trace 9 = 0))
    (hft : ∀ k, envF.trace (ftLeafLimb k) = coord b (GlobalCarryRecognizer.enc z (.atom a₀)).leaf k)
    (hfth : ∀ k, envF.trace (fthLeafLimb k) = coord b (GlobalCarryRecognizer.enc z (.atom a₉)).leaf k) :
    ∀ g ∈ axGates b, g.eval envF = 0 := by
  intro g hg
  simp only [axGates, List.mem_ofFn] at hg
  obtain ⟨k, rfl⟩ := hg
  have hc : ∀ a : ℕ, coord b ((a : ℕ) : K) k = (a : F) * coord b 1 k := by
    intro a
    rw [show ((a : ℕ) : K) = algebraMap F K (a : F) by rw [map_natCast],
      Algebra.algebraMap_eq_smul_one]
    simp [coord, map_smul]
  rw [axGateCoord_eval, hft, hfth, enc_atom_leaf, enc_atom_leaf, hc, hc]
  rcases hsel with ⟨h0, h9, ha⟩ | ⟨h0, h9, ha⟩ | ⟨h0, h9⟩ <;> rw [h0, h9] <;> (try rw [ha]) <;> ring

/-- `honestAx` reads the skeleton only (receipt of the shape). -/
theorem honestAx_s0 (h : Noun) (a : ℕ) (v : SemanticStrategy.ComputeRowSkeleton)
    (hs : v.state = .s0) (hf : v.formula = .cell h (.atom a)) : honestAx v = a := by
  simp [honestAx, hs, hf]

theorem honestAx_s9 (h c : Noun) (a : ℕ) (v : SemanticStrategy.ComputeRowSkeleton)
    (hs : v.state = .s9) (hf : v.formula = .cell h (.cell (.atom a) c)) : honestAx v = a := by
  simp [honestAx, hs, hf]

end honest

/-! ## 5. (iii): column `221` is read by no gate of `vclGates` — the bounded support facts -/

section support
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- Columns of the 309 chip outside Form R and below `309`. -/
def P309 (i : ℕ) : Prop := NoFormR i ∧ i < 309

theorem p309_base {i : ℕ} (h : i < 202) : P309 i := ⟨Or.inl h, by omega⟩

theorem typedCompile_colsIn309 (b : Basis (Fin 3) F K) :
    ∀ (t : CorrectedFinalTypedExpr), tNoCert t = true → ∀ k : Fin 3,
      ColsIn P309 (correctedFinalTypedCompile b t k)
  | .baseCur i, _, k => colsIn_mul (colsIn_var _ _ (p309_base (by have := i.isLt; omega))) (colsIn_const _)
  | .baseNext i, _, k => colsIn_mul (colsIn_var _ _ (p309_base (by have := i.isLt; omega))) (colsIn_const _)
  | .extCur i, _, k => colsIn_var _ _ (p309_base (by
      have := i.isLt; have := k.isLt; simp only [correctedFinalExtCoordIndex]; omega))
  | .extNext i, _, k => colsIn_var _ _ (p309_base (by
      have := i.isLt; have := k.isLt; simp only [correctedFinalExtCoordIndex]; omega))
  | .challenge i, _, k => by simp [correctedFinalTypedCompile, ColsIn, colsOf]
  | .extensionPublic i, _, k => by simp [correctedFinalTypedCompile, ColsIn, colsOf]
  | .scalarPublic i, _, k => by
      simp only [correctedFinalTypedCompile]
      exact colsIn_mul (by simp [ColsIn, colsOf]) (colsIn_const _)
  | .const c, _, k => colsIn_const _
  | .add x y, h, k => by
      simp only [tNoCert, Bool.and_eq_true] at h
      exact colsIn_add (typedCompile_colsIn309 b x h.1 k) (typedCompile_colsIn309 b y h.2 k)
  | .sub x y, h, k => by
      simp only [tNoCert, Bool.and_eq_true] at h
      exact colsIn_sub (typedCompile_colsIn309 b x h.1 k) (typedCompile_colsIn309 b y h.2 k)
  | .neg x, h, k => colsIn_neg (typedCompile_colsIn309 b x h k)
  | .mul x y, h, k => by
      simp only [tNoCert, Bool.and_eq_true] at h
      exact colsIn_mulVec b _ _ (fun i => typedCompile_colsIn309 b x h.1 i)
        (fun i => typedCompile_colsIn309 b y h.2 i) k
  | .pow x n, h, k => colsIn_powVec b _ (fun i => typedCompile_colsIn309 b x h i) n k
  | .certBase i, h, k => by simp [tNoCert] at h
  | .certExt i, h, k => by simp [tNoCert] at h
  | .lamPow d, _, k => by
      simp only [correctedFinalTypedCompile]
      split
      · exact colsIn_powVec b _ (fun i => by simp [ColsIn, colsOf]) _ k
      · exact colsIn_const _
  | .expCur, _, k => colsIn_mul (colsIn_var _ _ ⟨Or.inr (by omega), by omega⟩) (colsIn_const _)

theorem compile309_colsIn309 (b : Basis (Fin 3) F K) :
    ∀ (t : WTyped), wNoCert t = true → ∀ k : Fin 3, ColsIn P309 (compile309 b t k)
  | .leaf t, h, k => typedCompile_colsIn309 b t h k
  | .wCur j, _, k => colsIn_var _ _ ⟨Or.inr (by simp only [walkLimb]; omega),
      (walkLimb_range j k).2⟩
  | .wNext j, _, k => colsIn_var _ _ ⟨Or.inr (by simp only [walkLimb]; omega),
      (walkLimb_range j k).2⟩
  | .add x y, h, k => by
      simp only [wNoCert, Bool.and_eq_true] at h
      exact colsIn_add (compile309_colsIn309 b x h.1 k) (compile309_colsIn309 b y h.2 k)
  | .sub x y, h, k => by
      simp only [wNoCert, Bool.and_eq_true] at h
      exact colsIn_sub (compile309_colsIn309 b x h.1 k) (compile309_colsIn309 b y h.2 k)
  | .neg x, h, k => colsIn_neg (compile309_colsIn309 b x h k)
  | .mul x y, h, k => by
      simp only [wNoCert, Bool.and_eq_true] at h
      exact colsIn_mulVec b _ _ (fun i => compile309_colsIn309 b x h.1 i)
        (fun i => compile309_colsIn309 b y h.2 i) k
  | .pow x n, h, k => colsIn_powVec b _ (fun i => compile309_colsIn309 b x h i) n k

theorem residualWitnessCoord_colsIn309 (j : ResidualWitnessId) (k : Fin 3) :
    ColsIn P309 (residualWitnessCoord (F := F) j k) := by
  refine colsIn_var _ _ (p309_base ?_)
  have := j.isLt; have := k.isLt
  simp only [OptimizedComputeFinal.finalExtCoordIndex, OptimizedComputeFinal.residualWitnessRole]; omega

theorem notLastCoeff_colsIn309 : ColsIn P309 (notLastCoeff (F := F)) :=
  colsIn_sub (colsIn_const _) (colsIn_var _ _ (p309_base (by omega)))

theorem correctedCoreCoord309_colsIn309 (b : Basis (Fin 3) F K) (i : CorrectedCoreExtGateId)
    (hi : i ∈ keptCoreIds) (k : Fin 3) : ColsIn P309 (correctedCoreCoord309 b i k) := by
  unfold correctedCoreCoord309
  split
  · exact compile309_colsIn309 b _ queueNonEmpty309_noCert k
  split
  · exact compile309_colsIn309 b _ queueTiling309_noCert k
  have hg := typedCompile_colsIn309 b _ (ext_gates_noCert i hi) k
  unfold correctedCoreCoord
  split
  · exact colsIn_mul notLastCoeff_colsIn309 (residualWitnessCoord_colsIn309 _ _)
  split
  · exact colsIn_mul notLastCoeff_colsIn309 (residualWitnessCoord_colsIn309 _ _)
  split
  · exact typedCompile_colsIn309 b _ accAfterChain_noCert k
  split
  · exact colsIn_mul notLastCoeff_colsIn309 hg
  · exact hg

theorem keptGates309_colsIn309 (n : ℕ) (b : Basis (Fin 3) F K) :
    ∀ g ∈ keptGates309 n b, ColsIn P309 g := by
  have hv : ∀ i, i < 202 → ColsIn P309 (CoeffExpr.var (F := F) .traceCur i) := fun i hi =>
    colsIn_var _ _ (p309_base hi)
  intro g hg
  simp only [keptGates309, List.mem_append] at hg
  rcases hg with ((((hb | hc) | ha) | h2) | h4) | heq
  · have hsb : ∀ i, i < 202 → ColsIn P309 (selectorBool (F := F) i) := fun i hi =>
      colsIn_mul (hv i hi) (colsIn_sub (colsIn_const _) (hv i hi))
    have hf : ColsIn P309 (isFirstVar (F := F)) := hv 11 (by omega)
    have hl : ColsIn P309 (isLastVar (F := F)) := hv 12 (by omega)
    simp only [finalBaseTransitionGates, List.mem_append, List.mem_map, List.mem_range,
      List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with ⟨i, hi, rfl⟩ | rfl | rfl | rfl | rfl
    · exact hsb i (by omega)
    · exact colsIn_sub (colsIn_sumList _ _ fun i hi => hv i (by simp at hi; omega)) (colsIn_const _)
    · exact colsIn_mul hf (colsIn_sub (colsIn_const _) hf)
    · exact colsIn_mul hl (colsIn_sub (colsIn_const _) hl)
    · unfold endpointOverlapConsistency
      split
      · exact colsIn_sub (colsIn_mul hf hl) (colsIn_const _)
      · exact colsIn_mul hf hl
  · simp only [correctedCoreVCL, List.mem_flatten, List.mem_map] at hc
    obtain ⟨_, ⟨i, hi, rfl⟩, hc⟩ := hc
    rw [List.mem_ofFn] at hc
    obtain ⟨k, rfl⟩ := hc
    exact correctedCoreCoord309_colsIn309 b i hi k
  · simp only [correctedAux309, List.mem_flatten, List.mem_ofFn] at ha
    obtain ⟨_, ⟨j, rfl⟩, ha⟩ := ha
    rw [List.mem_ofFn] at ha
    obtain ⟨k, rfl⟩ := ha
    unfold correctedAuxCoord309
    split
    · rename_i h
      unfold correctedAuxCoord
      simp only [h, if_true]
      exact typedCompile_colsIn309 b _ accAfterStep_noCert k
    · exact colsIn_sub (residualWitnessCoord_colsIn309 _ _)
        (compile309_colsIn309 b _ (residualSource309_noCert _) k)
  · simp only [compileList309, List.mem_flatMap, List.mem_ofFn] at h2
    obtain ⟨t, ht, ⟨k, rfl⟩⟩ := h2
    exact compile309_colsIn309 b t (endpoint2_noCert t ht) k
  · simp only [compileList309, List.mem_flatMap, List.mem_ofFn] at h4
    obtain ⟨t, ht, ⟨k, rfl⟩⟩ := h4
    exact compile309_colsIn309 b t (endpoint4_noCert t ht) k
  · simp only [finalEndpointEqualityChecks, List.mem_append, List.mem_map, List.mem_range] at heq
    rcases heq with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;>
    · refine colsIn_mul (hv _ (by omega)) (colsIn_sub (hv _ (by omega)) ?_)
      intro j hj; simp [colsOf] at hj

theorem colsOf_reindexE (e : CoeffExpr F) : colsOf (reindexE e) = (colsOf e).map vclCol := by
  induction e with
  | const c => rfl
  | var k i => cases k <;> rfl
  | add a b ha hb => simp [reindexE, colsOf, ha, hb]
  | sub a b ha hb => simp [reindexE, colsOf, ha, hb]
  | mul a b ha hb => simp [reindexE, colsOf, ha, hb]
  | neg a ha => simp [reindexE, colsOf, ha]
  | pow a n ha => simp [reindexE, colsOf, ha]

theorem vclCol_ne_ax {i : ℕ} (h : P309 i) : vclCol i ≠ axCol := by
  obtain ⟨hn, hl⟩ := h
  simp only [NoFormR] at hn
  simp only [vclCol, serialCol, axCol]; split_ifs <;> omega

/-- **Column `221` is read by no gate of `vclGates`.** -/
theorem vclGates_not_ax (n : ℕ) (b : Basis (Fin 3) F K) :
    ∀ g ∈ vclGates n b, ∀ i ∈ colsOf g, i ≠ axCol := by
  intro g hg i hi
  simp only [vclGates, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨g', hg', rfl⟩ | hs
  · rw [colsOf_reindexE, List.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    exact vclCol_ne_ax (keptGates309_colsIn309 n b g' hg' j hj)
  · simp only [serialGates, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · have hc : colsOf (serialInitGate (F := F)) = [11, 220] := rfl
      rw [hc] at hi
      exact (by decide : ∀ j ∈ [11, 220], j ≠ axCol) i hi
    · have hc : colsOf (serialStepGate (F := F)) = [12, 220, 220] := rfl
      rw [hc] at hi
      exact (by decide : ∀ j ∈ [12, 220, 220], j ≠ axCol) i hi

/-- Evaluation depends only on the columns read. -/
theorem eval_congr_cols {F : Type*} [Field F] (e : CoeffExpr F) (env env' : Env F)
    (h : ∀ i ∈ colsOf e, env.trace i = env'.trace i ∧ env.traceNext i = env'.traceNext i)
    (hch : env.chal = env'.chal) (hp : env.pub = env'.pub) : e.eval env = e.eval env' := by
  induction e with
  | const c => rfl
  | var k i =>
      cases k
      · exact (h i (by simp [colsOf])).1
      · exact (h i (by simp [colsOf])).2
      · simp [CoeffExpr.eval, hch]
      · simp [CoeffExpr.eval, hp]
  | add a b ha hb =>
      simp only [CoeffExpr.eval]
      rw [ha (fun i hi => h i (by simp [colsOf, hi])), hb (fun i hi => h i (by simp [colsOf, hi]))]
  | sub a b ha hb =>
      simp only [CoeffExpr.eval]
      rw [ha (fun i hi => h i (by simp [colsOf, hi])), hb (fun i hi => h i (by simp [colsOf, hi]))]
  | mul a b ha hb =>
      simp only [CoeffExpr.eval]
      rw [ha (fun i hi => h i (by simp [colsOf, hi])), hb (fun i hi => h i (by simp [colsOf, hi]))]
  | neg a ha => simp only [CoeffExpr.eval]; rw [ha h]
  | pow a n ha => simp only [CoeffExpr.eval]; rw [ha h]

/-- Overwrite the axis column of an environment (current and next row). -/
def setAx {F : Type*} (env : Env F) (w : F) : Env F where
  trace := Function.update env.trace axCol w
  traceNext := Function.update env.traceNext axCol w
  chal := env.chal
  pub := env.pub

/-- Every `vclGates` gate is blind to the axis column. -/
theorem vclGates_set_ax (n : ℕ) (b : Basis (Fin 3) F K) (env : Env F) (w : F) :
    ∀ g ∈ vclGates n b, g.eval (setAx env w) = g.eval env := by
  intro g hg
  refine eval_congr_cols g (setAx env w) env (fun i hi => ?_) rfl rfl
  have hne := vclGates_not_ax n b g hg i hi
  simp [setAx, Function.update_of_ne hne]

end support

section nc
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **(iii) the NC: with the axis gate dropped a wrong axis is served.**  Take any row env on which
the gates of `computeChipVCL` vanish, in state `s0`, whose decoded `f_t.leaf` is the atom `n`.
Overwrite `ax` by `n + 1`: every `vclGates` gate still vanishes and the decoded leaf is unchanged, but
the B0 key axis is `n + 1 ≠ n` — and the real gate rejects the overwritten row. -/
theorem nc_ax_gate_dropped (n0 : ℕ) (b : Basis (Fin 3) F K) (env : Env F) (n : ℕ)
    (hn : n + 1 < ringChar F) (hacc : ∀ g ∈ vclGates n0 b, g.eval env = 0)
    (h0 : env.trace 0 = 1) (h9 : env.trace 9 = 0)
    (hleaf : (StrategyOfTracesLift.decodeDec (gatherCorrectedFinalTypedEnv b env)).f_t.leaf = (n : K)) :
    let env' := setAx env ((n + 1 : ℕ) : F)
    (∀ g ∈ vclGates n0 b, g.eval env' = 0) ∧
      (StrategyOfTracesLift.decodeDec (gatherCorrectedFinalTypedEnv b env')).f_t.leaf = (n : K) ∧
      natLift (env'.trace axCol) = n + 1 ∧
      ¬ ∀ g ∈ axGates b, g.eval env' = 0 := by
  intro env'
  have h221 : env'.trace axCol = ((n + 1 : ℕ) : F) := by simp [env', setAx]
  have hlf : (StrategyOfTracesLift.decodeDec (gatherCorrectedFinalTypedEnv b env')).f_t.leaf =
      (StrategyOfTracesLift.decodeDec (gatherCorrectedFinalTypedEnv b env)).f_t.leaf := by
    rw [decodeDec_ft_leaf, decodeDec_ft_leaf, gather_ext41, gather_ext41]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : ftLeafLimb k ≠ axCol := by simp only [ftLeafLimb, axCol]; omega
    simp [env', setAx, Function.update_of_ne this]
  refine ⟨fun g hg => by rw [vclGates_set_ax n0 b env _ g hg]; exact hacc g hg, hlf.trans hleaf,
    by rw [h221, natLift_natCast hn], fun hg => ?_⟩
  have h0' : env'.trace 0 = 1 := by simp [env', setAx, axCol, h0]
  have h9' : env'.trace 9 = 0 := by simp [env', setAx, axCol, h9]
  have := axGate_ax0 b env' hg h0' h9' n (by omega) (hlf.trans hleaf)
  rw [h221, natLift_natCast hn] at this
  omega

end nc

/-! ## 6. The repaired chip -/

section gatesA
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The gates of the repaired chip: `vclGates` and the three axis gates. -/
def vclGatesA (n : ℕ) (b : Basis (Fin 3) F K) : List (CoeffExpr F) := vclGates n b ++ axGates b

theorem vclGatesA_length (n : ℕ) (b : Basis (Fin 3) F K) : (vclGatesA n b).length = 312 := by
  simp [vclGatesA, vclGates_length]

theorem vclGatesA_degree (n : ℕ) (b : Basis (Fin 3) F K) : ∀ g ∈ vclGatesA n b, g.degree ≤ 4 := by
  intro g hg
  simp only [vclGatesA, List.mem_append] at hg
  rcases hg with h | h
  · exact vclGates_degree n b g h
  · exact (axGates_degree b g h).trans (by decide)

end gatesA

def vclRAPA {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) : RAP F :=
  { e := 3
    k := 2
    wRAP := ![vclRound0, 14]
    w := vclWidthA
    w_eq := by simp [Fin.sum_univ_two, vclRound0, vclWidthA]
    h := h
    d := 4
    s := (vclGatesA n b).length
    ω := orbit.ω
    β := orbit.βcoset
    I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
    C := fun i => coeffToMv chalVal pubVal ((vclGatesA n b).get i)
    C_vars := fun _i => coeffToMv_vars chalVal pubVal _
    C_deg := fun _i => (coeffToMv_totalDegree_le chalVal pubVal _).trans
      (vclGatesA_degree n b _ (List.get_mem _ _))
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

/-- **`computeChipVCLA`**: `computeChipVCL` plus the axis column `221` and its three gates. -/
def computeChipVCLA
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) : FixedPreprocessingRAP F where
  rap := vclRAPA (n := n) b chalVal pubVal orbit (rowNodeSet nodes)
  rounds_pos := by norm_num [vclRAPA]
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

theorem computeChipVCLA_sat_iff
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLA hn nodes b chalVal pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLA hn nodes b chalVal pubVal orbit) P ↔
      (computeChipVCLA hn nodes b chalVal pubVal orbit).BindsPreprocessing P ∧
        ∀ x ∈ rowNodeSet nodes, ∀ g ∈ vclGatesA n b,
          g.eval (Reify.envOfTrace P orbit.ω x chalVal pubVal) = 0 := by
  have key : ∀ (i : Fin (computeChipVCLA hn nodes b chalVal pubVal orbit).rap.s) (x : F),
      ((computeChipVCLA hn nodes b chalVal pubVal orbit).rap.compose P i).eval x =
        ((vclGatesA n b).get i).eval (Reify.envOfTrace P orbit.ω x chalVal pubVal) := by
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

theorem vclRAPA_fingerprint
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    let R := vclRAPA (n := n) b chalVal pubVal orbit H
    R.w = 222 ∧ R.s = 312 ∧ R.d = 4 ∧ R.k = 2 ∧ R.e = 3 ∧ R.wRAP = ![208, 14] :=
  ⟨rfl, vclGatesA_length n b, rfl, rfl, rfl, rfl⟩

/-! ## 7. The path key at B0 -/

/-- The compute table of the repaired chip. -/
def tableVCLA (h : ℕ) : TableSpec where
  width := vclWidthA
  colRound := fun j => colRoundVCL j
  height := h

theorem colRoundVCLA_zero_iff : ∀ c : Fin 222, colRoundVCL c = 0 ↔ (IsB0VCL c ∨ (c : ℕ) = axCol) := by
  unfold IsB0VCL axCol; decide +kernel

def vIdxB0A (h : ℕ) (j : Fin 2) : {c : Fin (tableVCLA h).width // (tableVCLA h).colRound c = 0} :=
  ⟨⟨vIdxCol j, by have := j.isLt; simp only [tableVCLA, vclWidthA, vIdxCol]; omega⟩, colRoundVCL_vIdx j⟩

def axB0 (h : ℕ) : {c : Fin (tableVCLA h).width // (tableVCLA h).colRound c = 0} :=
  ⟨⟨axCol, by simp only [tableVCLA, vclWidthA, axCol]; omega⟩, colRoundVCL_ax⟩

/-- The repaired key type: export `(cell serial, side)` or path `(root serial, axis)`. -/
abbrev KeyVCLA := (ℕ × Bool) ⊕ (ℕ × ℕ)

section pathKey
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The path request record of a row at lookup `j` (`m_p = 8` over `K`): six fingerprint
coordinates `(root, child)` (round-1 roles, given), slot `6` the B0 axis column, slot `7` the root
cell's serial `vIdxCol j`. -/
def pathRecOfRow (fps : Fin 6 → K) (envF : Env F) (j : Fin 2) : Fin 8 → K :=
  fun k => if hk : (k : ℕ) < 6 then fps ⟨k, hk⟩
    else if (k : ℕ) = 6 then algebraMap F K (envF.trace axCol)
    else algebraMap F K (envF.trace (vIdxCol j))

/-- `RecordView.key` at the path accumulator. -/
def keyOfPathRec (r : Fin 8 → K) : KeyVCLA := .inr (natLift (r 7), natLift (r 6))

/-- **`recKey` at a path lookup**: the B0 columns `vIdxCol j` and `221`, by type. -/
def recKeyPath {h : ℕ} (x : F) (b : B0Cols F (tableVCLA h)) (j : Fin 2) : KeyVCLA :=
  .inr (natLift (algebraMap F K ((b (vIdxB0A h j)).eval x)),
    natLift (algebraMap F K ((b (axB0 h)).eval x)))

/-- **The path key clause is B0** (one row, any trace, any node). -/
theorem path_key_clause {h : ℕ} (Q : Fin (tableVCLA h).width → F[X]) (ω x : F) (chal pub : ℕ → F)
    (fps : Fin 6 → K) (j : Fin 2) :
    keyOfPathRec (pathRecOfRow fps (Reify.envOfTrace Q ω x chal pub) j) =
      recKeyPath (K := K) x (b0 (T := tableVCLA h) Q) j := by
  have hj : vIdxCol j < (tableVCLA h).width := by
    have := j.isLt; simp only [tableVCLA, vclWidthA, vIdxCol]; omega
  have ha : axCol < (tableVCLA h).width := by simp only [tableVCLA, vclWidthA, axCol]; omega
  simp only [keyOfPathRec, pathRecOfRow, recKeyPath, b0, vIdxB0A, axB0, Reify.envOfTrace,
    dif_pos hj, dif_pos ha]
  rfl

end pathKey

end

end VclL.Compute
end Nock.NockVMROM.Thm54
