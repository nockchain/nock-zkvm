import Nock.NockVMROM.Thm54.VclL.Compute.TowerCoins
import Nock.NockVMROM.Thm54.VclL.Compute.ChipQ7S

/-!
# The slot records and the slot invariants at `Quad δ`

.

The `export_invQ7S` / `path_invQ7S` analogues at `Kio := Quad δ`: at a row with a one-hot state, the
three tower slot gates (`slot0Q`, `slot1Q`, `slot2Q` vanish at the gathered environment) give, for
every ACTIVE export slot `s < 3` (resp. path slot `s < 2`),
`inv′_s · compress(coinsQ)(rec′_s) = 1` with the `𝕂′` records `recXQ` (11 wide, side appended) and
`recPQ` (8 wide), and the activity flags `actXQ` / `actPQ` in `𝔽 ⊂ 𝕂′`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.ComputeTable (State)
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

section Recs
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **The `𝕂′` export record of slot `s`** (11 wide, the side appended: `1` at slot `0`). -/
def recXQ (eK : Env K) (eF : Env F) : ℕ → Fin 11 → Quad (algebraMap F K δ)
  | 0 => fun c => Q.val δ (recQ0 F c) eK eF
  | 1 => Fin.snoc (α := fun _ => Quad (algebraMap F K δ)) (recValQ δ eK eF tailRec) 0
  | _ => Fin.snoc (α := fun _ => Quad (algebraMap F K δ)) (recValQ δ eK eF ttRec) 0

/-- **The `𝕂′` path record of slot `s`** (8 wide). -/
def recPQ (eK : Env K) (eF : Env F) : ℕ → Fin 8 → Quad (algebraMap F K δ)
  | 0 => recValQ δ eK eF op0PathRec
  | _ => recValQ δ eK eF op9PathRec

/-- The export slot activities in `𝔽 ⊂ 𝕂′`. -/
def actXQ (eF : Env F) : ℕ → Quad (algebraMap F K δ)
  | 0 => 1
  | 1 => algebraMap F _ ((selSum (F := F) slot1ExportSels).eval eF)
  | 2 => algebraMap F _ (eF.trace 6)
  | _ => 0

/-- The path slot activities : `s0·(1 − z1)` / `s9·(1 − z1)`. -/
def actPQ (eF : Env F) : ℕ → Quad (algebraMap F K δ)
  | 0 => algebraMap F _ (eF.trace 0 * (1 - eF.trace z1Col))
  | 1 => algebraMap F _ (eF.trace 9 * (1 - eF.trace z1Col))
  | _ => 0

/-- The `𝕂′` inverse of export slot `s`. -/
def invXQ (eK : Env K) (eF : Env F) : ℕ → Quad (algebraMap F K δ)
  | 0 => Q.val δ (invQ F inv0Base (invImBase 0)) eK eF
  | 1 => Q.val δ (invQ F (lookupInvBase 0) (invImBase 1)) eK eF
  | _ => Q.val δ (invQ F (lookupInvBase 1) (invImBase 2)) eK eF

/-- The `𝕂′` inverse of path slot `s`. -/
def invPQ (eK : Env K) (eF : Env F) : ℕ → Quad (algebraMap F K δ)
  | 0 => Q.val δ (invQ F (lookupInvBase 0) (invImBase 1)) eK eF
  | _ => Q.val δ (invQ F (lookupInvBase 1) (invImBase 2)) eK eF

theorem sel_val (eK : Env K) (eF : Env F) (i : ℕ) :
    Q.val δ (qlift F (selVar i)) eK eF = algebraMap F _ (eF.trace i) := by
  rw [qlift_val]; rfl

theorem selSum_val (eK : Env K) (eF : Env F) (l : List ℕ) :
    Q.val δ (qlift F (selSum l)) eK eF = algebraMap F _ ((selSum (F := F) l).eval eF) :=
  qlift_val δ eK eF _

theorem actP0_val (eK : Env K) (eF : Env F) :
    Q.val δ (qlift F (actP0 F)) eK eF = algebraMap F _ (eF.trace 0 * (1 - eF.trace z1Col)) := by
  rw [qlift_val]; rfl

theorem actP9_val (eK : Env K) (eF : Env F) :
    Q.val δ (qlift F (actP9 F)) eK eF = algebraMap F _ (eF.trace 9 * (1 - eF.trace z1Col)) := by
  rw [qlift_val]; rfl

variable {δ}

theorem algebraMap_Q_inj : Function.Injective (algebraMap F (Quad (algebraMap F K δ))) :=
  (algebraMap F (Quad (algebraMap F K δ))).injective

/-- Active export slot at a one-hot row: the slot equation. -/
theorem export_invQ7T (eK : Env K) (eF : Env F) (st : State) (hst : SelAt eF st)
    (h0 : Q.IsZero (slot0Q F δ) eK eF) (h1 : Q.IsZero (slot1Q F δ) eK eF)
    (h2 : Q.IsZero (slot2Q F δ) eK eF) (s : ℕ) (hs : s < 3) (ha : actXQ (K := K) δ eF s = 1) :
    invXQ δ eK eF s * FiniteIO.compress (coinsQ δ eK eF) (recXQ δ eK eF s) = 1 := by
  have ht := selAt_trace hst
  rcases s with _ | _ | _ | s
  · exact slot0Q_sound δ eK eF h0
  · have ha' : (selSum (F := F) slot1ExportSels).eval eF = 1 := by
      apply algebraMap_Q_inj (δ := δ) (K := K); rw [map_one]; exact ha
    have hx : st = .s2 ∨ st = .s5 ∨ st = .s6 ∨ st = .s7 ∨ st = .s8 ∨ st = .s9 := by
      simp only [selSum_eval, slot1ExportSels, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil] at ha'
      rw [ht 2 (by norm_num), ht 5 (by norm_num), ht 6 (by norm_num), ht 7 (by norm_num),
        ht 8 (by norm_num), ht 9 (by norm_num)] at ha'
      cases st <;> simp [selIdx] at ha' ⊢
    have h00 : eF.trace 0 = 0 := by
      rw [ht 0 (by norm_num)]; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [selIdx]
    have e := slot1Q_sound δ eK eF h1
    rw [actP0_val, selSum_val, h00, ha', zero_mul, map_zero, zero_mul, zero_add, map_one, one_mul,
      zero_add] at e
    show invXQ δ eK eF 1 * FiniteIO.compress (coinsQ δ eK eF)
      (Fin.snoc (α := fun _ => Quad (algebraMap F K δ)) (recValQ δ eK eF tailRec) 0) = 1
    rw [compress_snoc, mul_zero, add_zero]
    exact e
  · have ha' : eF.trace 6 = 1 := by
      apply algebraMap_Q_inj (δ := δ) (K := K); rw [map_one]; exact ha
    have h6 : st = .s6 := by
      rw [ht 6 (by norm_num)] at ha'
      cases st <;> simp [selIdx] at ha' ⊢
    subst h6
    have h9 : eF.trace 9 = 0 := by rw [ht 9 (by norm_num)]; simp [selIdx]
    have e := slot2Q_sound δ eK eF h2
    rw [sel_val, actP9_val, h9, ha', zero_mul, map_zero, zero_mul, add_zero, map_one, one_mul,
      add_zero] at e
    show invXQ δ eK eF 2 * FiniteIO.compress (coinsQ δ eK eF)
      (Fin.snoc (α := fun _ => Quad (algebraMap F K δ)) (recValQ δ eK eF ttRec) 0) = 1
    rw [compress_snoc, mul_zero, add_zero]
    exact e
  · omega

/-- Active path slot at a one-hot row: the slot equation. -/
theorem path_invQ7T (eK : Env K) (eF : Env F) (st : State) (hst : SelAt eF st)
    (h1 : Q.IsZero (slot1Q F δ) eK eF)
    (h2 : Q.IsZero (slot2Q F δ) eK eF) (s : ℕ) (hs : s < 2) (ha : actPQ (K := K) δ eF s = 1) :
    invPQ δ eK eF s * FiniteIO.compress (coinsQ δ eK eF) (recPQ δ eK eF s) = 1 := by
  have ht := selAt_trace hst
  rcases s with _ | _ | s
  · have ha' : eF.trace 0 * (1 - eF.trace z1Col) = 1 := by
      apply algebraMap_Q_inj (δ := δ) (K := K); rw [map_one]; exact ha
    have h0 : st = .s0 := by
      by_contra hne
      rw [ht 0 (by norm_num)] at ha'
      cases st <;> simp [selIdx] at ha' hne
    subst h0
    have hx : (selSum (F := F) slot1ExportSels).eval eF = 0 := by
      simp only [selSum_eval, slot1ExportSels, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      rw [ht 2 (by norm_num), ht 5 (by norm_num), ht 6 (by norm_num), ht 7 (by norm_num),
        ht 8 (by norm_num), ht 9 (by norm_num)]
      simp [selIdx]
    have e := slot1Q_sound δ eK eF h1
    rw [actP0_val, selSum_val, hx, ha', map_zero, zero_mul, add_zero, map_one, one_mul,
      add_zero] at e
    exact e
  · have ha' : eF.trace 9 * (1 - eF.trace z1Col) = 1 := by
      apply algebraMap_Q_inj (δ := δ) (K := K); rw [map_one]; exact ha
    have h9 : st = .s9 := by
      by_contra hne
      rw [ht 9 (by norm_num)] at ha'
      cases st <;> simp [selIdx] at ha' hne
    subst h9
    have h6 : eF.trace 6 = 0 := by rw [ht 6 (by norm_num)]; simp [selIdx]
    have e := slot2Q_sound δ eK eF h2
    rw [sel_val, actP9_val, h6, ha', map_zero, zero_mul, zero_add, map_one, one_mul,
      zero_add] at e
    exact e
  · omega

end Recs

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
