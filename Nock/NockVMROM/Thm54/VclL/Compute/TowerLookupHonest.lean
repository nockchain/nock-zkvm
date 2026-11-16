import Nock.NockVMROM.Thm54.VclL.Compute.TowerBridge
import Nock.NockVMROM.Thm54.VclL.Compute.TowerC2cBase
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemReq

/-!

Generic in the env: every gate result is stated over an env whose columns meet NAMED placement
hypotheses (the honest VCL-only columns), the same style as C2a / C2c.

* `slot0Q_honest` / `slot1Q_honest` / `slot2Q_honest`: `slotkQ` vanishes at the honest inverse
  `inv′ = (den′)⁻¹` of the active slot's record and the one-hot state `s`, under the NAMED honestBad
  pole conditions (`den′ ≠ 0` at the active record) — `lookupGatesT_honest`.
* `serialGates_honest`: the serial column `220` is the row index.
* `honest_axGates'`, `honest_axImGates`: the ax gate, restated with the leaf hypotheses CONDITIONAL on the
  active state (the existing `honest_axGates` demands `f_t` AND `f_th` leaves be atom fingerprints at
  every row, which no honest non-OP0/OP9 row meets).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework
open Nock.NockVMROM.Thm54.VclL.Compute.LnRead
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. One-hot state selectors -/

section OneHot
variable {F : Type} [Field F]

/-- A listed selector sum at a one-hot state: `1` if the state is listed, else `0`. -/
theorem selSum_eval_oh (E : Env F) (s : ℕ) (hsel : ∀ j, j < 11 → E.trace j = if j = s then 1 else 0)
    (l : List ℕ) (hl : l.Nodup) (hlt : ∀ j ∈ l, j < 11) :
    (selSum l : CoeffExpr F).eval E = if s ∈ l then 1 else 0 := by
  rw [selSum, CoeffExpr.eval_sumList]
  induction l with
  | nil => simp
  | cons a l ih =>
    have hnd := List.nodup_cons.mp hl
    have ih' := ih hnd.2 (fun j hj => hlt j (List.mem_cons_of_mem _ hj))
    simp only [List.map_cons, List.sum_cons, selVar, CoeffExpr.eval] at ih' ⊢
    rw [hsel a (hlt a (List.mem_cons_self))]
    by_cases has : a = s
    · subst has
      have : a ∉ l := hnd.1
      simp [this] at ih' ⊢
      exact ih'
    · simp only [has, if_false, zero_add, ih']
      by_cases hsl : s ∈ l <;> simp [hsl, Ne.symm has]

theorem selVar_eval_oh (E : Env F) (s : ℕ) (hsel : ∀ j, j < 11 → E.trace j = if j = s then 1 else 0)
    (j : ℕ) (hj : j < 11) : (selVar j : CoeffExpr F).eval E = if j = s then 1 else 0 := by
  simp [selVar, CoeffExpr.eval, hsel j hj]

end OneHot

/-! ## 2. The slot gates at the honest inverse -/

section Slots
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- `Q.val` of the lifted selector sum at a one-hot state. -/
theorem qlift_selSum_oh (eK : Env K) (eF : Env F) (s : ℕ)
    (hsel : ∀ j, j < 11 → eF.trace j = if j = s then 1 else 0) (l : List ℕ) (hl : l.Nodup)
    (hlt : ∀ j ∈ l, j < 11) :
    Q.val δ (qlift F (selSum l)) eK eF = if s ∈ l then 1 else 0 := by
  rw [qlift_val, selSum_eval_oh eF s hsel l hl hlt]
  split_ifs <;> simp

theorem qlift_selVar_oh (eK : Env K) (eF : Env F) (s : ℕ)
    (hsel : ∀ j, j < 11 → eF.trace j = if j = s then 1 else 0) (j : ℕ) (hj : j < 11) :
    Q.val δ (qlift F (selVar j)) eK eF = if j = s then 1 else 0 := by
  rw [qlift_val, selVar_eval_oh eF s hsel j hj]
  split_ifs <;> simp

/-- The slot-0 denominator `den₀′` (the compressed formula-cell record at the `𝕂′` coins). -/
def den0Q (eK : Env K) (eF : Env F) : Quad (algebraMap F K δ) :=
  FiniteIO.compress (coinsQ δ eK eF) (fun c => Q.val δ (recQ0 F c) eK eF)

/-- **Slot 0 at the honest inverse**: `inv₀′ = (den₀′)⁻¹` and `den₀′ ≠ 0` (honestBad pole event)
give `inv₀′ · den₀′ − 1 = 0`. -/
theorem slot0Q_honest (eK : Env K) (eF : Env F)
    (hinv : Q.val δ (invQ F inv0Base (invImBase 0)) eK eF = (den0Q δ eK eF)⁻¹)
    (hne : den0Q δ eK eF ≠ 0) : Q.IsZero (slot0Q F δ) eK eF := by
  rw [Q.isZero_iff δ eK eF, slot0Q, qsub_val, qmul_val, qconst_val, ← compress_denQ δ eK eF 11 (recQ0 F)]
  rw [hinv]
  have : den0Q δ eK eF = FiniteIO.compress (coinsQ δ eK eF) (fun c => Q.val δ (recQ0 F c) eK eF) := rfl
  rw [← this, inv_mul_cancel₀ hne]; simp

/-- The slot-1 denominator `s0 · den_path + (Σ s_x) · den_export`. -/
def den1Q (eK : Env K) (eF : Env F) : Quad (algebraMap F K δ) :=
  Q.val δ (qlift F (selVar 0)) eK eF *
      FiniteIO.compress (coinsQ δ eK eF) (recValQ δ eK eF op0PathRec) +
    Q.val δ (qlift F (selSum slot1ExportSels)) eK eF *
      FiniteIO.compress (coinsQ δ eK eF) (recValQ δ eK eF tailRec)

/-- The slot-2 denominator `s6 · den_tt + s9 · den_path9`. -/
def den2Q (eK : Env K) (eF : Env F) : Quad (algebraMap F K δ) :=
  Q.val δ (qlift F (selVar 6)) eK eF *
      FiniteIO.compress (coinsQ δ eK eF) (recValQ δ eK eF ttRec) +
    Q.val δ (qlift F (selVar 9)) eK eF *
      FiniteIO.compress (coinsQ δ eK eF) (recValQ δ eK eF op9PathRec)


theorem actP0_val_z0 (eK : Env K) (eF : Env F) (hz : eF.trace z1Col = 0 ∨ eF.trace 0 = 0) :
    Q.val δ (qlift F (actP0 F)) eK eF = Q.val δ (qlift F (selVar 0)) eK eF := by
  rw [qlift_val, qlift_val]; rcases hz with hz | hz <;> simp [actP0, notZ1, selVar, CoeffExpr.eval, hz]

theorem actP9_val_z0 (eK : Env K) (eF : Env F) (hz : eF.trace z1Col = 0 ∨ eF.trace 9 = 0) :
    Q.val δ (qlift F (actP9 F)) eK eF = Q.val δ (qlift F (selVar 9)) eK eF := by
  rw [qlift_val, qlift_val]; rcases hz with hz | hz <;> simp [actP9, notZ1, selVar, CoeffExpr.eval, hz]

/-- At a `z1 = 1` row the path activities vanish. -/
theorem actP0_val_z1 (eK : Env K) (eF : Env F) (hz : eF.trace z1Col = 1) :
    Q.val δ (qlift F (actP0 F)) eK eF = 0 := by
  rw [qlift_val]; simp [actP0, notZ1, selVar, CoeffExpr.eval, hz]

theorem actP9_val_z1 (eK : Env K) (eF : Env F) (hz : eF.trace z1Col = 1) :
    Q.val δ (qlift F (actP9 F)) eK eF = 0 := by
  rw [qlift_val]; simp [actP9, notZ1, selVar, CoeffExpr.eval, hz]

theorem qlift_selSum_cons (eK : Env K) (eF : Env F) (a : ℕ) (l : List ℕ) :
    Q.val δ (qlift F (selSum (a :: l))) eK eF =
      Q.val δ (qlift F (selVar a)) eK eF + Q.val δ (qlift F (selSum l)) eK eF := by
  rw [qlift_val, qlift_val, qlift_val, ← map_add]
  congr 1


theorem z1Gates_of_zero (b : Basis (Fin 3) F K) (eF : Env F) (hz : eF.trace z1Col = 0) :
    ∀ g ∈ z1Gates b δ, g.eval eF = 0 := by
  have key : ∀ sel r c, ∀ g ∈ qGates b (z1EqQ F δ sel r c), g.eval eF = 0 := by
    intro sel r c
    refine (qGates_iff b (isCoordEnv_gather b eF) _).mpr ((Q.isZero_iff δ _ eF _).mpr ?_)
    rw [z1EqQ, qmul_val, qlift_val]
    simp [CoeffExpr.eval, hz]
  intro g hg
  simp only [z1Gates, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap] at hg
  rcases hg with ((rfl | rfl) | ⟨c, -, hg⟩) | ⟨c, -, hg⟩
  · simp [z1BoolGate, CoeffExpr.eval, hz]
  · simp [z1AxGate, CoeffExpr.eval, hz]
  · exact key _ _ _ g hg
  · exact key _ _ _ g hg

theorem slot1Q_of (eK : Env K) (eF : Env F) (hz : eF.trace z1Col = 0 ∨ eF.trace 0 = 0)
    (hinv : Q.val δ (invQ F (lookupInvBase 0) (invImBase 1)) eK eF = (den1Q δ eK eF)⁻¹)
    (h : (Q.val δ (qlift F (selSum (0 :: slot1ExportSels))) eK eF = 0 ∧ den1Q δ eK eF = 0) ∨
      (Q.val δ (qlift F (selSum (0 :: slot1ExportSels))) eK eF = 1 ∧ den1Q δ eK eF ≠ 0)) :
    Q.IsZero (slot1Q F δ) eK eF := by
  rw [Q.isZero_iff δ eK eF, slot1Q, qsub_val, qmul_val, qadd_val, qmul_val, qmul_val, qadd_val,
    actP0_val_z0 δ eK eF hz, ← qlift_selSum_cons,
    ← compress_denQ δ eK eF 8 (recQ F op0PathRec), ← compress_denQ δ eK eF 10 (recQ F tailRec), hinv]
  have e : ∀ (m : ℕ) (r : Fin m → Entry), (fun c => Q.val δ (recQ F r c) eK eF) = recValQ δ eK eF r :=
    fun m r => rfl
  rw [e, e]
  show (den1Q δ eK eF)⁻¹ * den1Q δ eK eF - _ = 0
  rcases h with ⟨hA, hD⟩ | ⟨hA, hD⟩
  · rw [hA, hD]; simp
  · rw [hA, inv_mul_cancel₀ hD]; simp

theorem slot2Q_of (eK : Env K) (eF : Env F) (hz : eF.trace z1Col = 0 ∨ eF.trace 9 = 0)
    (hinv : Q.val δ (invQ F (lookupInvBase 1) (invImBase 2)) eK eF = (den2Q δ eK eF)⁻¹)
    (h : (Q.val δ (qlift F (selSum [6, 9])) eK eF = 0 ∧ den2Q δ eK eF = 0) ∨
      (Q.val δ (qlift F (selSum [6, 9])) eK eF = 1 ∧ den2Q δ eK eF ≠ 0)) :
    Q.IsZero (slot2Q F δ) eK eF := by
  have h69 : Q.val δ (qlift F (selVar 6)) eK eF + Q.val δ (qlift F (selVar 9)) eK eF =
      Q.val δ (qlift F (selSum [6, 9])) eK eF := by
    rw [qlift_selSum_cons, qlift_selSum_cons]
    simp [qlift_val, selSum, CoeffExpr.sumList, CoeffExpr.eval]
  rw [Q.isZero_iff δ eK eF, slot2Q, qsub_val, qmul_val, qadd_val, qmul_val, qmul_val, qadd_val,
    actP9_val_z0 δ eK eF hz, h69,
    ← compress_denQ δ eK eF 10 (recQ F ttRec), ← compress_denQ δ eK eF 8 (recQ F op9PathRec), hinv]
  have e : ∀ (m : ℕ) (r : Fin m → Entry), (fun c => Q.val δ (recQ F r c) eK eF) = recValQ δ eK eF r :=
    fun m r => rfl
  rw [e, e]
  show (den2Q δ eK eF)⁻¹ * den2Q δ eK eF - _ = 0
  rcases h with ⟨hA, hD⟩ | ⟨hA, hD⟩
  · rw [hA, hD]; simp
  · rw [hA, inv_mul_cancel₀ hD]; simp

theorem slot1ExportSels_nodup : (0 :: slot1ExportSels).Nodup := by decide
theorem slot1ExportSels_lt : ∀ j ∈ (0 :: slot1ExportSels), j < 11 := by decide

/-- **Slot 1 at one-hot state `s`**: the honest inverse `(den₁′)⁻¹` satisfies the gate, given the
pole conditions at the ACTIVE record only (`s = 0`: the path record; `s ∈ {2,5,6,7,8,9}`: the export
record); other states have `act = 0` and `den₁′ = 0`. -/
theorem slot1Q_honest (eK : Env K) (eF : Env F) (hz : eF.trace z1Col = 0 ∨ eF.trace z1Col = 1) (s : ℕ) (hs : s < 11)
    (hsel : ∀ j, j < 11 → eF.trace j = if j = s then 1 else 0)
    (hinv : Q.val δ (invQ F (lookupInvBase 0) (invImBase 1)) eK eF = (den1Q δ eK eF)⁻¹)
    (hp : s = 0 → FiniteIO.compress (coinsQ δ eK eF) (recValQ δ eK eF op0PathRec) ≠ 0)
    (he : s ∈ slot1ExportSels → FiniteIO.compress (coinsQ δ eK eF) (recValQ δ eK eF tailRec) ≠ 0) :
    Q.IsZero (slot1Q F δ) eK eF := by
  have hex : (slot1ExportSels).Nodup := by decide
  have hexlt : ∀ j ∈ slot1ExportSels, j < 11 := by decide
  have hA := qlift_selSum_oh δ eK eF s hsel (0 :: slot1ExportSels) slot1ExportSels_nodup slot1ExportSels_lt
  have hX := qlift_selSum_oh δ eK eF s hsel slot1ExportSels hex hexlt
  have h0 := qlift_selVar_oh δ eK eF s hsel 0 (by omega)
  by_cases hzs : eF.trace z1Col = 0 ∨ eF.trace 0 = 0
  · apply slot1Q_of δ eK eF hzs hinv
    unfold den1Q
    rw [hA, hX, h0]
    by_cases hs0 : s = 0
    · subst hs0
      have hn : (0 : ℕ) ∉ slot1ExportSels := by decide
      right; simp [hn]; exact hp rfl
    · by_cases hse : s ∈ slot1ExportSels
      · right
        have : (0 : ℕ) ≠ s := fun h => hs0 h.symm
        simp [hse, this, hs0]; exact he hse
      · left
        have : (0 : ℕ) ≠ s := fun h => hs0 h.symm
        simp [hse, this, hs0]
  ·
    have hz1 : eF.trace z1Col = 1 := by
      rcases hz with h | h
      · exact absurd (Or.inl h) hzs
      · exact h
    have hs0 : s = 0 := by
      have h1 := hsel 0 (by norm_num)
      by_contra hne
      exact hzs (Or.inr (by rw [h1, if_neg (fun h => hne h.symm)]))
    subst hs0
    have hn : (0 : ℕ) ∉ slot1ExportSels := by decide
    rw [Q.isZero_iff δ eK eF, slot1Q, qsub_val, qmul_val, qadd_val, qmul_val, qmul_val, qadd_val,
      actP0_val_z1 δ eK eF hz1, hX]
    simp [hn]

/-- **Slot 2 at one-hot state `s`** (`s6` export / `s9` core path). -/
theorem slot2Q_honest (eK : Env K) (eF : Env F) (hz : eF.trace z1Col = 0 ∨ eF.trace z1Col = 1) (s : ℕ) (hs : s < 11)
    (hsel : ∀ j, j < 11 → eF.trace j = if j = s then 1 else 0)
    (hinv : Q.val δ (invQ F (lookupInvBase 1) (invImBase 2)) eK eF = (den2Q δ eK eF)⁻¹)
    (h6 : s = 6 → FiniteIO.compress (coinsQ δ eK eF) (recValQ δ eK eF ttRec) ≠ 0)
    (h9 : s = 9 → FiniteIO.compress (coinsQ δ eK eF) (recValQ δ eK eF op9PathRec) ≠ 0) :
    Q.IsZero (slot2Q F δ) eK eF := by
  have hA := qlift_selSum_oh δ eK eF s hsel [6, 9] (by decide) (by decide)
  have h6' := qlift_selVar_oh δ eK eF s hsel 6 (by omega)
  have h9' := qlift_selVar_oh δ eK eF s hsel 9 (by omega)
  by_cases hzs : eF.trace z1Col = 0 ∨ eF.trace 9 = 0
  · apply slot2Q_of δ eK eF hzs hinv
    unfold den2Q
    rw [hA, h6', h9']
    by_cases a6 : s = 6
    · subst a6
      right; simp; exact h6 rfl
    · by_cases a9 : s = 9
      · subst a9
        right; simp; exact h9 rfl
      · left
        have n6 : (6 : ℕ) ≠ s := fun h => a6 h.symm
        have n9 : (9 : ℕ) ≠ s := fun h => a9 h.symm
        simp [a6, a9, n6, n9]
  ·
    have hz1 : eF.trace z1Col = 1 := by
      rcases hz with h | h
      · exact absurd (Or.inl h) hzs
      · exact h
    have hs9 : s = 9 := by
      have h1 := hsel 9 (by norm_num)
      by_contra hne
      exact hzs (Or.inr (by rw [h1, if_neg (fun h => hne h.symm)]))
    subst hs9
    rw [Q.isZero_iff δ eK eF, slot2Q, qsub_val, qmul_val, qadd_val, qmul_val, qmul_val, qadd_val,
      actP9_val_z1 δ eK eF hz1, h6']
    simp

/-- **`lookupGatesT` at honest data**: the three slot equations at the honest inverses, one-hot state
`s`, under the three NAMED pole conditions (`den′ ≠ 0` at the active record of each slot). -/
theorem lookupGatesT_honest (b : Basis (Fin 3) F K) (envF : Env F) (hz : envF.trace z1Col = 0 ∨ envF.trace z1Col = 1)
    (s : ℕ) (hs : s < 11)
    (hsel : ∀ j, j < 11 → envF.trace j = if j = s then 1 else 0)
    (hinv0 : Q.val δ (invQ F inv0Base (invImBase 0)) (gatherEnv b envF) envF =
      (den0Q δ (gatherEnv b envF) envF)⁻¹)
    (hinv1 : Q.val δ (invQ F (lookupInvBase 0) (invImBase 1)) (gatherEnv b envF) envF =
      (den1Q δ (gatherEnv b envF) envF)⁻¹)
    (hinv2 : Q.val δ (invQ F (lookupInvBase 1) (invImBase 2)) (gatherEnv b envF) envF =
      (den2Q δ (gatherEnv b envF) envF)⁻¹)
    (hne0 : den0Q δ (gatherEnv b envF) envF ≠ 0)
    (hp : s = 0 → FiniteIO.compress (coinsQ δ (gatherEnv b envF) envF)
      (recValQ δ (gatherEnv b envF) envF op0PathRec) ≠ 0)
    (he : s ∈ slot1ExportSels → FiniteIO.compress (coinsQ δ (gatherEnv b envF) envF)
      (recValQ δ (gatherEnv b envF) envF tailRec) ≠ 0)
    (h6 : s = 6 → FiniteIO.compress (coinsQ δ (gatherEnv b envF) envF)
      (recValQ δ (gatherEnv b envF) envF ttRec) ≠ 0)
    (h9 : s = 9 → FiniteIO.compress (coinsQ δ (gatherEnv b envF) envF)
      (recValQ δ (gatherEnv b envF) envF op9PathRec) ≠ 0) :
    ∀ g ∈ lookupGatesT b δ, g.eval envF = 0 :=
  (lookupGatesT_iff δ b envF).mpr
    ⟨slot0Q_honest δ _ _ hinv0 hne0, slot1Q_honest δ _ _ hz s hs hsel hinv1 hp he,
      slot2Q_honest δ _ _ hz s hs hsel hinv2 h6 h9⟩

end Slots

/-! ## 3. Serial and ax gates -/

section SerialAx
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **`serialGates` at honest data**: column `220` is the row index `i` (next row `i+1` off the last
row), masks `11 / 12` the first / last indicators of `n` rows. -/
theorem serialGates_honest (n i : ℕ) (hi : i < n) (E : Env F)
    (h11 : E.trace 11 = if i = 0 then 1 else 0) (h12 : E.trace 12 = if i + 1 = n then 1 else 0)
    (hS : E.trace serialCol = (i : F)) (hSn : i + 1 < n → E.traceNext serialCol = ((i + 1 : ℕ) : F)) :
    ∀ g ∈ (serialGates : List (CoeffExpr F)), g.eval E = 0 := by
  intro g hg
  simp only [serialGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · rw [serialInitGate_eval]
    by_cases h0 : i = 0
    · right; rw [hS, h0]; simp
    · left; rw [h11]; simp [h0]
  · rw [serialStepGate_eval]
    by_cases hl : i + 1 = n
    · left; rw [h12]; simp [hl]
    · right; rw [hSn (by omega), hS]; push_cast; ring

/-- **NC for the serial gate**: a serial column that skips (`i + 2` at the next row) is rejected. -/
theorem serialStep_rejects_skip (E : Env F) (hF : (1 : F) ≠ 0) (h12 : E.trace 12 = 0)
    (hS : E.traceNext serialCol = E.trace serialCol + 2) :
    (serialStepGate (F := F)).eval E ≠ 0 := by
  rw [Ne, serialStepGate_eval]
  rintro (h | h)
  · rw [h12] at h; exact zero_ne_one h
  · have : (2 : F) = 1 := by linear_combination hS.symm.trans h
    have h1 : (1 : F) = 0 := by linear_combination this
    exact hF h1

/-- **`honest_axGates'`**: the ax gate at honest data with the leaf hypotheses CONDITIONAL on the
active state (the existing `honest_axGates` needs both `f_t` and `f_th` to be atom fingerprints at
every row, which a non-OP0/OP9 row does not meet). -/
theorem honest_axGates' [FiniteDimensional F K] (b : Basis (Fin 3) F K) (z : K) (a₀ a₉ : ℕ) (envF : Env F)
    (hsel0 : envF.trace 0 = 0 ∨ envF.trace 0 = 1) (hsel9 : envF.trace 9 = 0 ∨ envF.trace 9 = 1)
    (h0 : envF.trace 0 = 1 → envF.trace axCol = (a₀ : F) ∧
      ∀ k, envF.trace (ftLeafLimb k) = coord b (GlobalCarryRecognizer.enc z (.atom a₀)).leaf k)
    (h9 : envF.trace 9 = 1 → envF.trace axCol = (a₉ : F) ∧
      ∀ k, envF.trace (fthLeafLimb k) = coord b (GlobalCarryRecognizer.enc z (.atom a₉)).leaf k) :
    ∀ g ∈ axGates b, g.eval envF = 0 := by
  intro g hg
  simp only [axGates, List.mem_ofFn] at hg
  obtain ⟨k, rfl⟩ := hg
  have hc : ∀ a : ℕ, coord b ((a : ℕ) : K) k = (a : F) * coord b 1 k := by
    intro a
    rw [show ((a : ℕ) : K) = algebraMap F K (a : F) by rw [map_natCast],
      Algebra.algebraMap_eq_smul_one]
    simp [coord, map_smul]
  rw [axGateCoord_eval]
  have e0 : envF.trace 0 * (envF.trace (ftLeafLimb k) - envF.trace axCol * coord b 1 k) = 0 := by
    rcases hsel0 with h | h
    · rw [h]; ring
    · obtain ⟨ha, hf⟩ := h0 h
      rw [hf, enc_atom_leaf, hc, ha]; ring
  have e9 : envF.trace 9 * (envF.trace (fthLeafLimb k) - envF.trace axCol * coord b 1 k) = 0 := by
    rcases hsel9 with h | h
    · rw [h]; ring
    · obtain ⟨ha, hf⟩ := h9 h
      rw [hf, enc_atom_leaf, hc, ha]; ring
  rw [e0, e9]; ring

/-- **`axImGates` at honest data**: the Im halves of the `f_t` / `f_th` leaves vanish on the active
atom-test row (an atom's leaf is `𝔽`-valued). -/
theorem honest_axImGates (envF : Env F)
    (h0 : envF.trace 0 = 0 ∨ ∀ k : Fin 3, envF.trace ((fullImMap.ext 41).getD 0 + (k : ℕ)) = 0)
    (h9 : envF.trace 9 = 0 ∨ ∀ k : Fin 3, envF.trace ((fullImMap.ext 44).getD 0 + (k : ℕ)) = 0) :
    ∀ g ∈ (axImGates : List (CoeffExpr F)), g.eval envF = 0 := by
  intro g hg
  simp only [axImGates, List.mem_ofFn] at hg
  obtain ⟨k, rfl⟩ := hg
  simp only [axImGateCoord, CoeffExpr.eval]
  rcases h0 with h | h <;> rcases h9 with h' | h'
  · rw [h, h']; ring
  · rw [h, h' k]; ring
  · rw [h', h k]; ring
  · rw [h k, h' k]; ring

end SerialAx

/-! ## 4. Accumulator gates at a prefix-sum fill -/

section Acc
variable {F : Type} [Field F]

/-- **`accGates` at honest data (coordinate level).**  Row `i` of `N`; the accumulator limb `k` holds
the exclusive prefix sum `Σ_{j<i} T j k` of the per-row term coordinates, the next row holds the next
prefix, the term gate coordinate evaluates to `T i k`, and the public terminal limb is the total. -/
theorem accGates_prefix (e : ℕ) (slots : List (Slot F)) (accBase pubBase N i : ℕ) (hi : i < N)
    (E : Env F) (T : ℕ → ℕ → F)
    (h11 : E.trace 11 = if i = 0 then 1 else 0) (h12 : E.trace 12 = if i + 1 = N then 1 else 0)
    (hterm : ∀ k < e, (termCoord slots k).eval E = T i k)
    (hacc : ∀ k < e, E.trace (accBase + k) = ∑ j ∈ Finset.range i, T j k)
    (haccN : i + 1 < N → ∀ k < e, E.traceNext (accBase + k) = ∑ j ∈ Finset.range (i + 1), T j k)
    (hpub : ∀ k < e, E.pub (pubBase + k) = ∑ j ∈ Finset.range N, T j k) :
    ∀ g ∈ accGates e slots accBase pubBase, g.eval E = 0 := by
  intro g hg
  simp only [accGates, List.mem_append, List.mem_map, List.mem_range] at hg
  rcases hg with (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩
  · simp only [accInitGate, CoeffExpr.eval, h11, hacc k hk]
    by_cases h0 : i = 0 <;> simp [h0]
  · simp only [accStepGate, CoeffExpr.eval, h12, hterm k hk, hacc k hk]
    by_cases hl : i + 1 = N
    · simp [hl]
    · rw [haccN (by omega) k hk, Finset.sum_range_succ]; simp [hl]
  · simp only [accTermGate, CoeffExpr.eval, h12, hterm k hk, hacc k hk, hpub k hk]
    by_cases hl : i + 1 = N
    · subst hl
      rw [Finset.sum_range_succ]; simp
    · simp [hl]

/-- **NC for the accumulator**: a terminal public off by one from the total fails the terminal gate on
the last row. -/
theorem accTerm_rejects_wrong_terminal (e : ℕ) (slots : List (Slot F)) (accBase pubBase : ℕ)
    (E : Env F) (hF : (1 : F) ≠ 0) (k : ℕ) (hk : k < e) (h12 : E.trace 12 = 1)
    (hpub : E.pub (pubBase + k) = E.trace (accBase + k) + (termCoord slots k).eval E + 1) :
    ∃ g ∈ accGates e slots accBase pubBase, g.eval E ≠ 0 := by
  refine ⟨accTermGate slots accBase pubBase k, ?_, ?_⟩
  · simp only [accGates, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inr ⟨k, hk, rfl⟩
  · simp only [accTermGate, CoeffExpr.eval, h12, hpub]
    intro h
    apply hF
    linear_combination -h

end Acc

section AccK
variable {F Kio : Type} [Field F] [Field Kio] [Algebra F Kio] {e : ℕ} (bio : Basis (Fin e) F Kio)

theorem coord_sum (s : Finset ℕ) (f : ℕ → Kio) (k : Fin e) :
    coord bio (∑ j ∈ s, f j) k = ∑ j ∈ s, coord bio (f j) k := by
  simp only [coord, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]

/-- **The accumulator gates at a prefix-sum fill, `Kio` level**: accumulator limbs are the coordinates of
the exclusive prefix `Σ_{j<i} termVal`, the public limbs those of the total `ρ`. -/
theorem accGates_prefixK (slots : List (Slot F)) (accBase pubBase N i : ℕ) (hi : i < N)
    (envs : ℕ → Env F) (ρ : Kio)
    (h11 : (envs i).trace 11 = if i = 0 then 1 else 0)
    (h12 : (envs i).trace 12 = if i + 1 = N then 1 else 0)
    (hacc : ∀ k : Fin e, (envs i).trace (accBase + k) =
      coord bio (∑ j ∈ Finset.range i, termVal bio slots (envs j)) k)
    (haccN : i + 1 < N → ∀ k : Fin e, (envs i).traceNext (accBase + k) =
      coord bio (∑ j ∈ Finset.range (i + 1), termVal bio slots (envs j)) k)
    (hpub : ∀ k : Fin e, (envs i).pub (pubBase + k) = coord bio ρ k)
    (hρ : ∑ j ∈ Finset.range N, termVal bio slots (envs j) = ρ) :
    ∀ g ∈ accGates e slots accBase pubBase, g.eval (envs i) = 0 := by
  classical
  refine accGates_prefix e slots accBase pubBase N i hi (envs i)
    (fun j k => if h : k < e then coord bio (termVal bio slots (envs j)) ⟨k, h⟩ else 0) h11 h12 ?_ ?_ ?_ ?_
  · intro k hk
    simp only [hk, dif_pos]
    rw [← coord_termVal bio slots (envs i) ⟨k, hk⟩]
  · intro k hk
    have := hacc ⟨k, hk⟩
    simp only [hk, dif_pos]
    rw [this, coord_sum]
  · intro hl k hk
    have := haccN hl ⟨k, hk⟩
    simp only [hk, dif_pos]
    rw [this, coord_sum]
  · intro k hk
    have := hpub ⟨k, hk⟩
    simp only [hk, dif_pos]
    rw [this, ← hρ, coord_sum]

end AccK

section AccQ2
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K)

/-- **`accGatesT` at honest data.**  Row `i` of `N`; the Re / Im accumulator limbs of the export
(`226`, `403`) and path (`229`, `406`) accumulators are the prefix sums of the per-row `𝕂′` terms, and the
`ρ′` publics (`42 / 51`, `45 / 54`) are the coordinates of the totals `rx`, `rp ∈ 𝕂′`, which are the sums of
the row terms. -/
theorem accGatesT_honest (N i : ℕ) (hi : i < N) (envs : ℕ → Env F) (rx rp : Quad (algebraMap F K δ))
    (h11 : (envs i).trace 11 = if i = 0 then 1 else 0)
    (h12 : (envs i).trace 12 = if i + 1 = N then 1 else 0)
    (hrx : ∑ j ∈ Finset.range N, termQ δ b accSlotsX accSlotsXIm (envs j) = rx)
    (hrp : ∑ j ∈ Finset.range N, termQ δ b accSlotsPT accSlotsPImT (envs j) = rp)
    (haX : ∀ k : Fin 3, (envs i).trace (accExportBase + k) =
      coord b (∑ j ∈ Finset.range i, termVal b accSlotsX (envs j)) k)
    (haXn : i + 1 < N → ∀ k : Fin 3, (envs i).traceNext (accExportBase + k) =
      coord b (∑ j ∈ Finset.range (i + 1), termVal b accSlotsX (envs j)) k)
    (haXI : ∀ k : Fin 3, (envs i).trace (accImExport + k) =
      coord b (∑ j ∈ Finset.range i, termVal b accSlotsXIm (envs j)) k)
    (haXIn : i + 1 < N → ∀ k : Fin 3, (envs i).traceNext (accImExport + k) =
      coord b (∑ j ∈ Finset.range (i + 1), termVal b accSlotsXIm (envs j)) k)
    (haP : ∀ k : Fin 3, (envs i).trace (accPathBase + k) =
      coord b (∑ j ∈ Finset.range i, termVal b accSlotsPT (envs j)) k)
    (haPn : i + 1 < N → ∀ k : Fin 3, (envs i).traceNext (accPathBase + k) =
      coord b (∑ j ∈ Finset.range (i + 1), termVal b accSlotsPT (envs j)) k)
    (haPI : ∀ k : Fin 3, (envs i).trace (accImPath + k) =
      coord b (∑ j ∈ Finset.range i, termVal b accSlotsPImT (envs j)) k)
    (haPIn : i + 1 < N → ∀ k : Fin 3, (envs i).traceNext (accImPath + k) =
      coord b (∑ j ∈ Finset.range (i + 1), termVal b accSlotsPImT (envs j)) k)
    (hpx : ∀ k : Fin 3, (envs i).pub (rhoExportPub + k) = coord b (Quad.re _ rx) k)
    (hpxI : ∀ k : Fin 3, (envs i).pub (rhoExportImPub + k) = coord b (Quad.im _ rx) k)
    (hpp : ∀ k : Fin 3, (envs i).pub (rhoPathPub + k) = coord b (Quad.re _ rp) k)
    (hppI : ∀ k : Fin 3, (envs i).pub (rhoPathImPub + k) = coord b (Quad.im _ rp) k) :
    ∀ g ∈ (accGatesT : List (CoeffExpr F)), g.eval (envs i) = 0 := by
  have sX := hrx; have sP := hrp
  unfold termQ at sX sP
  rw [sum_mk] at sX sP
  have rxRe : ∑ j ∈ Finset.range N, termVal b accSlotsX (envs j) = Quad.re _ rx := by
    rw [← sX, Quad.re_mk]
  have rxIm : ∑ j ∈ Finset.range N, termVal b accSlotsXIm (envs j) = Quad.im _ rx := by
    rw [← sX, Quad.im_mk]
  have rpRe : ∑ j ∈ Finset.range N, termVal b accSlotsPT (envs j) = Quad.re _ rp := by
    rw [← sP, Quad.re_mk]
  have rpIm : ∑ j ∈ Finset.range N, termVal b accSlotsPImT (envs j) = Quad.im _ rp := by
    rw [← sP, Quad.im_mk]
  intro g hg
  simp only [accGatesT, List.mem_append] at hg
  rcases hg with ((hg | hg) | hg) | hg
  · exact accGates_prefixK b accSlotsX accExportBase rhoExportPub N i hi envs _ h11 h12 haX haXn hpx rxRe g hg
  · exact accGates_prefixK b _ accImExport rhoExportImPub N i hi envs _ h11 h12 haXI haXIn hpxI rxIm g hg
  · exact accGates_prefixK b accSlotsPT accPathBase rhoPathPub N i hi envs _ h11 h12 haP haPn hpp rpRe g hg
  · exact accGates_prefixK b accSlotsPImT accImPath rhoPathImPub N i hi envs _ h11 h12 haPI haPIn hppI rpIm g hg

end AccQ2

/-! ## 5. The terminals: `honestReq` in the closed form of `MF.req_eq` -/

section Req
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.TraceGen
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))]


def honestReqCF (γ ρ z : Quad (algebraMap F K δF)) (cells : List Noun) (preads reads : List (Noun × ℕ)) :
    Fin 3 → Quad (algebraMap F K δF)
  | 0 => 0
  | 1 => ((shallowSided reads).map fun c =>
      (FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xReq δF z cells c.1 c.2))⁻¹).sum
  | 2 => (((preads.filter fun r => isPathAx r.2)).map fun r =>
      (FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (pReq δF z cells r))⁻¹).sum

/-- **`CF.honestReq = MF.honestReq`** at every accumulator: the closed form equals the memory
side's terminal `H.req`, given the two named facts — `hslot` (every deep read has a defined slot) and
`hv`. -/
theorem honestReqCF_eq_req {hT hP hC : ℕ} [DecidableEq F] [Fintype F] [DecidableEq K]
    [DecidableEq (Quad (algebraMap F K δF))]
    (H : HonestVCL (K := K) δF hT hP hC) (χ : Coins frameVCL K)
    (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome) (hv : H.vReqs χ = []) (a : Fin 3) :
    H.req χ a = honestReqCF (γC χ) (ρC χ) (zC χ) H.d.cells H.d.preads H.d.reads a := by
  rw [H.req_eq χ hslot a]
  fin_cases a
  · show (List.map _ (H.vReqs χ)).sum = _
    rw [hv]; first | rfl | simp only [List.map_nil, List.sum_nil, honestReqCF]
  · show (List.map _ (H.xReqs χ)).sum = _
    simp only [HonestVCL.xReqs, honestReqCF]; erw [List.map_map]; rfl
  · show (List.map _ (H.pReqs χ)).sum = _
    simp only [HonestVCL.pReqs, honestReqCF]; erw [List.map_map]; rfl

/-- The sum over rows of per-row list sums is the sum over the concatenation. -/
theorem sum_range_flatMap {α M : Type*} [AddCommMonoid M] (N : ℕ) (L : ℕ → List α) (g : α → M) :
    ∑ j ∈ Finset.range N, ((L j).map g).sum = (((List.range N).flatMap L).map g).sum := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.flatMap_append, List.map_append,
      List.sum_append]
    simp

/-- **Terminal equality (generic over the row lists)**: if row `j`'s `𝕂′` term is the sum of the
reciprocals of its records' compressions (`hrow`, the placement hypothesis: the inverse columns are
`(den′)⁻¹` of the closed-form records) and the rows' record lists concatenate to the demand's
(`hflat`), the sum of the row terms is the closed-form terminal. -/
theorem terminal_eq_closed {α : Type} {m : ℕ} (N : ℕ) (tq : ℕ → Quad (algebraMap F K δF))
    (γ ρ : Quad (algebraMap F K δF)) (L : ℕ → List α) (rec : α → Fin m → Quad (algebraMap F K δF))
    (hrow : ∀ j < N, tq j = ((L j).map fun a => (FiniteIO.compress (m := m) ⟨γ, ρ⟩ (rec a))⁻¹).sum)
    (R : List α) (hflat : (List.range N).flatMap L = R) :
    ∑ j ∈ Finset.range N, tq j = (R.map fun a => (FiniteIO.compress (m := m) ⟨γ, ρ⟩ (rec a))⁻¹).sum := by
  rw [← hflat, ← sum_range_flatMap]
  exact Finset.sum_congr rfl fun j hj => hrow j (Finset.mem_range.mp hj)

/-- `shallowSided` of concatenated read lists is the concatenation of the rows' `shallowSided`. -/
theorem shallowSided_flatMap {ι : Type} (rows : List ι) (keys : ι → List (Noun × ℕ)) :
    shallowSided (rows.flatMap keys) = rows.flatMap fun g => shallowSided (keys g) := by
  induction rows with
  | nil => simp [shallowSided, shallowReads]
  | cons g rs ih =>
    simp only [List.flatMap_cons] at ih ⊢
    simp only [shallowSided, shallowReads, List.filter_append, List.flatMap_append] at ih ⊢
    rw [ih]

/-- The deep reads (as filtered, no dedup) of concatenated read lists. -/
theorem deepFilter_flatMap {ι : Type} (rows : List ι) (keys : ι → List (Noun × ℕ)) :
    (rows.flatMap keys).filter (fun r => isDeep r.2) =
      rows.flatMap fun g => (keys g).filter fun r => isDeep r.2 := by
  induction rows with
  | nil => simp
  | cons g rs ih => simp only [List.flatMap_cons, List.filter_append, ih]

/-- SHD-A: the path-kind reads (as filtered, no dedup) of concatenated read lists. -/
theorem pathFilter_flatMap {ι : Type} (rows : List ι) (keys : ι → List (Noun × ℕ)) :
    (rows.flatMap keys).filter (fun r => isPathAx r.2) =
      rows.flatMap fun g => (keys g).filter fun r => isPathAx r.2 := by
  induction rows with
  | nil => simp
  | cons g rs ih => simp only [List.flatMap_cons, List.filter_append, ih]

end Req

/-! ## 6. The VCL-only fill and its placement -/

section Fill
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- The `𝕂`-limb `j - base` of `x` when `base ≤ j < base + 3`, else `0`. -/
def limbAt (b : Basis (Fin 3) F K) (x : K) (base j : ℕ) : F :=
  if h : base ≤ j ∧ j < base + 3 then coord b x ⟨j - base, by omega⟩ else 0

/-- **The honest VCL-only columns of a row** (`TowerRowVals.vcl`): serial `220`, ax `221`, `fIdx` `222`,
the root serials `202 / 203`, the Re limbs of the three slot inverses (`223..225`, `214..216`, `217..219`)
and of the two accumulators (`226..228`, `229..231`), and their
Im limbs `394..402` (inverses) and `403..408` (accumulators). -/
def vclFill (b : Basis (Fin 3) F K) (ser : F) (ax : ℕ) (fIdx vI0 vI1 : F)
    (inv0 inv1 inv2 accX accP : Quad (algebraMap F K δ)) (j : ℕ) : F :=
  if j = 220 then ser else if j = 221 then (ax : F) else if j = 222 then fIdx
  else if j = 202 then vI0 else if j = 203 then vI1
  else if j = z1Col then (if ax = 1 then 1 else 0)
  else limbAt b (Quad.re _ inv0) inv0Base j + limbAt b (Quad.re _ inv1) (lookupInvBase 0) j +
    limbAt b (Quad.re _ inv2) (lookupInvBase 1) j + limbAt b (Quad.re _ accX) accExportBase j +
    limbAt b (Quad.re _ accP) accPathBase j +
    limbAt b (Quad.im _ inv0) (invImBase 0) j + limbAt b (Quad.im _ inv1) (invImBase 1) j +
    limbAt b (Quad.im _ inv2) (invImBase 2) j + limbAt b (Quad.im _ accX) accImExport j +
    limbAt b (Quad.im _ accP) accImPath j


theorem vclFill_z1 (b : Basis (Fin 3) F K) ser (ax : ℕ) fIdx vI0 vI1 inv0 inv1 inv2 accX accP :
    vclFill (δ := δ) b ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP z1Col = if ax = 1 then 1 else 0 := by
  simp [vclFill, limbAt, z1Col, inv0Base, lookupInvBase, accExportBase, accPathBase, invImBase,
    accImExport, accImPath]

theorem vclFill_serial (b : Basis (Fin 3) F K) ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP :
    vclFill (δ := δ) b ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP serialCol = ser := by
  simp [vclFill, serialCol]
theorem vclFill_ax (b : Basis (Fin 3) F K) ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP :
    vclFill (δ := δ) b ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP axCol = (ax : F) := by
  simp [vclFill, axCol]
theorem vclFill_inv0 (b : Basis (Fin 3) F K) ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP (k : Fin 3) :
    vclFill (δ := δ) b ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP (inv0Base + k) =
      coord b (Quad.re _ inv0) k := by
  fin_cases k <;>
    simp [vclFill, limbAt, z1Col, inv0Base, lookupInvBase, accExportBase, accPathBase, invImBase, accImExport,
      accImPath, coord]

/-- The Im limbs of the slot-`j` inverse (`invImBase j`) in the honest VCL fill. -/
theorem vclFill_invIm (b : Basis (Fin 3) F K) ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP (k : Fin 3) :
    vclFill (δ := δ) b ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP (invImBase 0 + k) =
        coord b (Quad.im _ inv0) k ∧
      vclFill (δ := δ) b ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP (invImBase 1 + k) =
        coord b (Quad.im _ inv1) k ∧
      vclFill (δ := δ) b ser ax fIdx vI0 vI1 inv0 inv1 inv2 accX accP (invImBase 2 + k) =
        coord b (Quad.im _ inv2) k := by
  fin_cases k <;>
    simp [vclFill, limbAt, z1Col, inv0Base, lookupInvBase, accExportBase, accPathBase, invImBase, accImExport,
      accImPath, coord]

/-- `vclColT` reads the VCL-only columns from `TowerRowVals.vcl`. -/
theorem vclColT_vclOnly (b : Basis (Fin 3) F K) {n : ℕ} (rows : Fin n → TowerRowVals (K := K) δ)
    (i : Fin n) (j : ℕ) (h : 202 ≤ j) (h2 : j < 208 ∨ (214 ≤ j ∧ j < 232)) :
    vclColT b rows j i = (rows i).vcl j := by
  have h1 : ¬ j < 202 := by omega
  have h3 : ¬ ((208 ≤ j ∧ j < 214) ∨ (232 ≤ j ∧ j < 394)) := by omega
  simp [vclColT, h1, h3]

/-- **The Im inverse / accumulator columns are suppliable**: `vclColT` reads columns `394..408` from
`TowerRowVals.vcl`. -/
theorem vclColT_imVcl (b : Basis (Fin 3) F K) {n : ℕ} (rows : Fin n → TowerRowVals (K := K) δ)
    (i : Fin n) (j : ℕ) (h : 394 ≤ j) : vclColT b rows j i = (rows i).vcl j := by
  have h1 : ¬ j < 202 := by omega
  have h3 : ¬ ((208 ≤ j ∧ j < 214) ∨ (232 ≤ j ∧ j < 394)) := by omega
  simp [vclColT, h1, h3]

/-- **A `(Re, Im)` pair of `𝕂`-limb triples of the honest trace reads back its `𝕂′` value**: if the
VCL-only columns `re..re+2` / `im..im+2` of row `i` carry the coordinates of `Re x` / `Im x`, the
gathered `Q`-value of `invQ re im` at the row node is `x`. -/
theorem invQ_val_honestQT (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)
    (hinj : Function.Injective nodes) (rows : Fin n → TowerRowVals (K := K) δ)
    (ω : F) (cv pv : ℕ → F) (i : Fin n) (re im : ℕ) (hre : 202 ≤ re ∧ re + 3 ≤ 208 ∨
      214 ≤ re ∧ re + 3 ≤ 232) (him : 394 ≤ im ∧ im + 3 ≤ 409) (x : Quad (algebraMap F K δ))
    (hxr : ∀ k : Fin 3, (rows i).vcl (re + k) = coord b (Quad.re _ x) k)
    (hxi : ∀ k : Fin 3, (rows i).vcl (im + k) = coord b (Quad.im _ x) k) :
    Q.val δ (invQ F re im) (gatherEnv b (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv))
      (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv) = x := by
  set E := Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv
  have hw : vclWidthT = 410 := rfl
  have r1 : (gatherEnv b E).trace re = Quad.re _ x := by
    simp only [gatherEnv]
    apply LogUp.limbVal_eq_of_coords
    intro k
    rw [env_honestQT_trace b nodes hinj rows ω cv pv i (by rw [hw]; have := k.isLt; omega),
      vclColT_vclOnly b rows i _ (by omega) (by have := k.isLt; omega), hxr]
  have r2 : (gatherEnv b E).trace im = Quad.im _ x := by
    simp only [gatherEnv]
    apply LogUp.limbVal_eq_of_coords
    intro k
    rw [env_honestQT_trace b nodes hinj rows ω cv pv i (by rw [hw]; have := k.isLt; omega),
      vclColT_imVcl b rows i _ (by omega), hxi]
  show Quad.mk _ ((invQ F re im).1.eval (gatherEnv b E) E) ((invQ F re im).2.eval (gatherEnv b E) E) = x
  simp only [invQ, qcol, MixedExpr.eval]
  rw [r1, r2, Quad.mk_re_im]

/-- **Serial gates at the honest fill**: the VCL-only column `220` of row `i` is `i`, the masks come
from the base columns; row `i'` is the successor (`ω · x_i = x_i'`). -/
theorem serialGates_honestQT (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)
    (hinj : Function.Injective nodes) (rows : Fin n → TowerRowVals (K := K) δ)
    (ω : F) (cv pv : ℕ → F) (i : Fin n)
    (h11 : (rows i).base 11 = if (i : ℕ) = 0 then 1 else 0)
    (h12 : (rows i).base 12 = if (i : ℕ) + 1 = n then 1 else 0)
    (hser : ∀ i : Fin n, (rows i).vcl serialCol = ((i : ℕ) : F)) (i' : Fin n)
    (hadj : (i : ℕ) + 1 < n → ω * nodes i = nodes i' ∧ (i' : ℕ) = i + 1) :
    ∀ g ∈ (serialGates : List (CoeffExpr F)),
      g.eval (Reify.envOfTrace (honestQT b nodes rows vclWidthT) ω (nodes i) cv pv) = 0 := by
  have hs : vclColT b rows serialCol i = ((i : ℕ) : F) := by
    rw [vclColT_vclOnly b rows i serialCol (by decide) (by right; decide), hser]
  refine serialGates_honest n i i.isLt _ ?_ ?_ ?_ ?_
  · rw [env_honestQT_trace b nodes hinj rows ω cv pv i (by decide : 11 < vclWidthT)]
    simp [vclColT, srcColT, h11]
  · rw [env_honestQT_trace b nodes hinj rows ω cv pv i (by decide : 12 < vclWidthT)]
    simp [vclColT, srcColT, h12]
  · rw [env_honestQT_trace b nodes hinj rows ω cv pv i (by decide : serialCol < vclWidthT), hs]
  · intro hl
    obtain ⟨ha, hi'⟩ := hadj hl
    rw [envNext_honestQT_trace b nodes hinj rows ω cv pv i i' ha (by decide : serialCol < vclWidthT),
      vclColT_vclOnly b rows i' serialCol (by decide) (by right; decide), hser, hi']

end Fill

/-! ## 7. Negative controls -/

section NC
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **NC (discriminating)**: a wrong slot-1 inverse (`den₁′⁻¹ + 1`) on an active row (`act = 1`,
`den₁′ ≠ 0`) breaks `slot1Q`. -/
theorem slot1Q_wrong_inverse (eK : Env K) (eF : Env F) (hz : eF.trace z1Col = 0 ∨ eF.trace 0 = 0)
    (hA : Q.val δ (qlift F (selSum (0 :: slot1ExportSels))) eK eF = 1) (hD : den1Q δ eK eF ≠ 0)
    (hinv : Q.val δ (invQ F (lookupInvBase 0) (invImBase 1)) eK eF = (den1Q δ eK eF)⁻¹ + 1) :
    ¬ Q.IsZero (slot1Q F δ) eK eF := by
  intro h
  have := slot1Q_sound δ eK eF h
  have e : den1Q δ eK eF = _ := rfl
  rw [actP0_val_z0 δ eK eF hz, ← qlift_selSum_cons] at this
  rw [hinv] at this
  rw [hA] at this
  have h2 : ((den1Q δ eK eF)⁻¹ + 1) * den1Q δ eK eF = 1 := this
  rw [add_mul, inv_mul_cancel₀ hD, one_mul] at h2
  exact hD (by linear_combination h2)

end NC

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
