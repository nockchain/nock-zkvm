/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHAtomRow.lean

  One row of the atom chip at the executable data. -/
import Nock.V1J8.FillAtom
import Nock.V1J8.GenAtom
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomRow

/-! ## 1. Preliminary lemmas -/

theorem nodesOf_powN (q : ChipIn) (ho : OrbOK q) : nodesOf q = ComplJ8Of.powN (mkOrbit q ho) q.n :=
  funext fun i => nodesOf_eq q i

theorem enc_cons' {K : Type} [Field K] (z : K) (x y : Noun) :
    GlobalCarryRecognizer.enc z (Noun.cell x y) =
      ComputeTable.FP.cons z (GlobalCarryRecognizer.enc z x) (GlobalCarryRecognizer.enc z y) := by
  by_cases hz : z = 0
  · subst hz
    have hx1 : 1 ≤ x.leaves := x.one_le_leaves
    have h3 : NPR.listPoly (NPR.dyckBits (K := K) (Noun.cell x y))
        = Polynomial.X * NPR.listPoly (NPR.dyckBits (K := K) x) + Polynomial.X ^ (2 * x.leaves - 1)
          + Polynomial.X ^ (2 * x.leaves) * NPR.listPoly (NPR.dyckBits (K := K) y) := by
      simpa only [NPR.Φ_snd_snd] using NPR.Phi3_cons (K := K) x y
    have h2 : NPR.listPoly (NPR.leafF (K := K) (Noun.cell x y))
        = NPR.listPoly (NPR.leafF (K := K) x)
          + Polynomial.X ^ x.leaves * NPR.listPoly (NPR.leafF (K := K) y) := by
      simpa only [NPR.Φ_snd_fst] using NPR.Phi2_cons (K := K) x y
    have e1 : (0 : K) ^ x.leaves = 0 := zero_pow (by omega)
    have e2 : (0 : K) ^ (2 * x.leaves - 1) = 0 := zero_pow (by omega)
    have e3 : (0 : K) ^ (2 * x.leaves) = 0 := zero_pow (by omega)
    refine ComputeTable.FP.ext ?_ ?_ ?_
    · simp only [GlobalCarryRecognizer.enc_size, Noun.leaves, ComputeTable.FP.cons, pow_add]
    · simp only [GlobalCarryRecognizer.enc_dyck, GlobalCarryRecognizer.enc_size, ComputeTable.FP.cons]
      rw [h3]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_X_pow, e1, e2, e3]
      all_goals simp
    · simp only [GlobalCarryRecognizer.enc_leaf, GlobalCarryRecognizer.enc_size, ComputeTable.FP.cons]
      rw [h2]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X_pow, e1]
      all_goals simp
  · exact GlobalCarryRecognizer.enc_cons hz x y

/-- All leaves `< P`. -/
def Small : Noun → Prop
  | .atom a => a < P
  | .cell a b => Small a ∧ Small b

theorem toQ_encE_small (z y : K6) : ∀ n : Noun, Small n →
    (encE z y n).toQ = GlobalCarryRecognizer.enc (K6.toQ z) n
  | .atom a, h => by
      have hl : leafE y a = lq a := by simp only [leafE, lq]; rw [if_pos (show a < p from h)]
      show (⟨K6.toQ z, K6.toQ 0, K6.toQ (leafE y a)⟩ : ComputeTable.FP KQ) = _
      rw [GlobalCarryRecognizer.enc_atom, hl, toQ_lqN, K6.toQ_zero]; rfl
  | .cell a b, h => by
      show (consE z (encE z y a) (encE z y b)).toQ = _
      rw [enc_cons', ← toQ_encE_small z y a h.1, ← toQ_encE_small z y b h.2]
      simp only [consE, FPE.toQ, ComputeTable.FP.cons, K6.toQ_add, K6.toQ_mul, K6.toQ_inv]

section Coins
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]

theorem toQ_yE_zA (χe : CoinsE) : K6.toQ (yE χe) = ComplJ8Of.zA deltaF (toχ χe) := by
  rw [ComplJ8Of.zA, ChalsAZJ8.chalsAJ8Z_y]; rfl

theorem zAt_zE (χe : CoinsE) : Quad.mk _ (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe) 37)
    (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe) 38) = K6.toQ (zE χe) := by
  rw [ChalsAZJ8.chalsAJ8Z_zAt]; rfl

theorem coOfA_z (χe : CoinsE) : (coOfA χe).z = yE χe := rfl

theorem toQ_γVE (χe : CoinsE) : K6.toQ (γVE χe) = ComplJ8Of.γV deltaF (toχ χe) := rfl
theorem toQ_ρVE (χe : CoinsE) : K6.toQ (ρVE χe) = ComplJ8Of.ρV deltaF (toχ χe) := rfl
theorem toQ_γHE (χe : CoinsE) : K6.toQ (γHE χe) = ComplJ8Bad.γH deltaF (toχ χe) := rfl
theorem toQ_ρHE (χe : CoinsE) : K6.toQ (ρHE χe) = ComplJ8Bad.ρH deltaF (toχ χe) := rfl

end Coins

/-! ## 2. `hdN'/tlN'`, small atoms, the shape of an atom-table row -/

theorem hdN'_eq : hdN' = Nock.NockVMROM.Thm54.VclL.hdN := by funext n; cases n <;> rfl
theorem tlN'_eq : tlN' = Nock.NockVMROM.Thm54.VclL.tlN := by funext n; cases n <;> rfl

theorem B_lt_P : Nock.Atoms.B < P := by
  have := Nock.Atoms.two_B_lt_p
  change Nock.Atoms.B < Nock.Atoms.p
  omega

theorem small_combOf : ∀ l : List ℕ, (∀ a ∈ l, a < P) → Small (combOf l)
  | [], _ => show 0 < P from lt_of_le_of_lt (Nat.zero_le _) B_lt_P
  | [x], h => h x (by simp)
  | [x, y], h => ⟨h x (by simp), h y (by simp)⟩
  | x :: y :: z :: r, h =>
      ⟨h x (by simp), small_combOf (y :: z :: r) (fun a ha => h a (List.mem_cons_of_mem _ ha))⟩

/-- An atom-table row: the comb of a limb list of length `≥ 2` with all limbs `< B`. -/
def AtomRow (n : Noun) : Prop :=
  ∃ l : List ℕ, 2 ≤ l.length ∧ (∀ a ∈ l, a < Nock.Atoms.B) ∧ n = combOf l

theorem AtomRow.shape {n : Noun} (h : AtomRow n) : ∃ a t, n = .cell (.atom a) t ∧ a < P ∧ Small t := by
  obtain ⟨l, h2, hl, rfl⟩ := h
  have hlt : ∀ a ∈ l, a < P := fun a ha => lt_trans (hl a ha) B_lt_P
  match l, h2, hlt with
  | [], h, _ => simp at h
  | [x], h, _ => simp at h
  | [x, y], _, hlt => exact ⟨x, .atom y, rfl, hlt x (by simp), hlt y (by simp)⟩
  | x :: y :: z :: r, _, hlt =>
      exact ⟨x, combOf (y :: z :: r), rfl, hlt x (by simp),
        small_combOf _ (fun a ha => hlt a (List.mem_cons_of_mem _ ha))⟩

theorem AtomRow.small {n : Noun} (h : AtomRow n) : Small n := by
  obtain ⟨a, t, rfl, ha, ht⟩ := h.shape
  exact ⟨ha, ht⟩

/-- `small_of_acs`: every row of the atom cell list is an atom-table row. -/
theorem atomRow_of_acs (bigs : List ℕ) (dupP : Bool) (hbigs : ∀ a ∈ bigs, P ≤ a) (y : Noun)
    (hy : y ∈ ComplJ8Data.acsP P bigs dupP) : AtomRow y := by
  obtain ⟨l, h2, hc, rfl, -⟩ := ComplJ8Atom.shape_acsP bigs dupP hbigs y hy
  exact ⟨l, h2, hc.1, rfl⟩

theorem small_of_acs (bigs : List ℕ) (dupP : Bool) (hbigs : ∀ a ∈ bigs, P ≤ a) (y : Noun)
    (hy : y ∈ ComplJ8Data.acsP P bigs dupP) : Small y :=
  (atomRow_of_acs bigs dupP hbigs y hy).small

theorem hdl_small (acsL : List Noun) {v : ℕ} (h : v < P) :
    Nock.V1J8.Gen.hdl acsL (.atom v) = (0, v) := by
  simp [Nock.V1J8.Gen.hdl, h]

/-- The head of an atom-table row and its tail. -/
theorem small_head_tail {y : Noun} (h : AtomRow y) :
    ∃ a, a < P ∧ hdN' y = .atom a ∧ Small (tlN' y) := by
  obtain ⟨a, t, rfl, ha, ht⟩ := h.shape
  exact ⟨a, ha, rfl, ht⟩

/-! ## 3. Rank coin -/

section Rank
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]

theorem toQ_rkK (mu : ℕ) :
    K6.toQ (rkK mu) = Quad.mk _ (algebraMap (ZMod P) KC ((mu % 2 ^ 62 : ℕ) : ZMod P))
      (algebraMap (ZMod P) KC ((mu / 2 ^ 62 : ℕ) : ZMod P)) := by
  rw [rkK, toQ_mk, toK_g3, toK_g3, toZ_natG, toZ_natG]
  rfl

end Rank

/-! ## 4. The executable row's fields -/

section Fields
variable (pt : Noun → ℕ) (k : Co) (y : K6) (cs : List Noun) (n : Noun) (j : ℕ)

theorem cellDE_j : (cellDE pt k y cs n j).j = j := by
  unfold cellDE; dsimp only; split <;> rfl
theorem cellDE_pE : (cellDE pt k y cs n j).pE = encE k.z y n := by
  unfold cellDE; dsimp only; split <;> rfl
theorem cellDE_lE : (cellDE pt k y cs n j).lE = encE k.z y (hdN' n) := by
  unfold cellDE; dsimp only; split <;> rfl
theorem cellDE_rE : (cellDE pt k y cs n j).rE = encE k.z y (tlN' n) := by
  unfold cellDE; dsimp only; split <;> rfl
theorem cellDE_vInv : (cellDE pt k y cs n j).vInv =
    (compressE k.γ k.ρ ![(encE k.z y n).size, (encE k.z y n).dyck, (encE k.z y n).leaf, rkK n.internal, lq j])⁻¹ := by
  unfold cellDE; dsimp only; split <;> rfl
theorem cellDE_x0Inv : (cellDE pt k y cs n j).x0Inv =
    (compressE k.γ k.ρ ![(encE k.z y n).size, (encE k.z y n).dyck, (encE k.z y n).leaf,
      (encE k.z y (hdN' n)).size, (encE k.z y (hdN' n)).dyck, (encE k.z y (hdN' n)).leaf,
      (encE k.z y (tlN' n)).size, (encE k.z y (tlN' n)).dyck, (encE k.z y (tlN' n)).leaf, lq j, lq 0])⁻¹ := by
  unfold cellDE; dsimp only; split <;> rfl
theorem cellDE_x1Inv : (cellDE pt k y cs n j).x1Inv =
    (compressE k.γ k.ρ ![(encE k.z y n).size, (encE k.z y n).dyck, (encE k.z y n).leaf,
      (encE k.z y (hdN' n)).size, (encE k.z y (hdN' n)).dyck, (encE k.z y (hdN' n)).leaf,
      (encE k.z y (tlN' n)).size, (encE k.z y (tlN' n)).dyck, (encE k.z y (tlN' n)).leaf, lq j, lq 1])⁻¹ := by
  unfold cellDE; dsimp only; split <;> rfl
theorem cellDE_lInv (hl : (hdN' n).isCell = false) : (cellDE pt k y cs n j).lInv = 0 := by
  unfold cellDE; dsimp only; split <;> simp [cellD, hl]
theorem cellDE_rInv_cell (hr : (tlN' n).isCell = true) : (cellDE pt k y cs n j).rInv =
    (compressE k.γ k.ρ ![(encE k.z y (tlN' n)).size, (encE k.z y (tlN' n)).dyck, (encE k.z y (tlN' n)).leaf,
      rkK (tlN' n).internal, lq (pt n)])⁻¹ := by
  unfold cellDE; dsimp only; rw [if_pos hr]; rfl
theorem cellDE_rInv_atom (hr : (tlN' n).isCell = false) : (cellDE pt k y cs n j).rInv = 0 := by
  unfold cellDE; dsimp only; split <;> simp_all [cellD]

end Fields

/-! ## 5. The per-row bridges -/

section Row
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]

/-- The honest atom-table cell row. -/
noncomputable abbrev RB (z : KQ) (cs : List Noun) (mv mx : ℕ → ℕ) (pt : Noun → ℕ) (n : Noun) (j : ℕ) :
    CellVals (ZMod P) KQ :=
  ComplJ8Cell.cellRowBP deltaF z (fun _ => none) cs mv mx (fun _ => 0) pt n j

/-- Generic (abstract row) unfoldings of `cellFillInv`: cheap, no whnf on the big row. -/
theorem cfi_vInv (γ ρ : KQ) (c : CellVals (ZMod P) KQ) :
    (cellFillInv deltaF γ ρ c).vInv = (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf deltaF c))⁻¹ := rfl
theorem cfi_lInv (γ ρ : KQ) (c : CellVals (ZMod P) KQ) :
    (cellFillInv deltaF γ ρ c).lInv = liftQ deltaF c.wL * (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (lKeyOf deltaF c))⁻¹ := rfl
theorem cfi_rInv (γ ρ : KQ) (c : CellVals (ZMod P) KQ) :
    (cellFillInv deltaF γ ρ c).rInv = liftQ deltaF c.wR * (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (rKeyOf deltaF c))⁻¹ := rfl
theorem cfi_x0Inv (γ ρ : KQ) (c : CellVals (ZMod P) KQ) :
    (cellFillInv deltaF γ ρ c).x0Inv =
      (FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf deltaF c (0 : ZMod P)))⁻¹ := rfl
theorem cfi_x1Inv (γ ρ : KQ) (c : CellVals (ZMod P) KQ) :
    (cellFillInv deltaF γ ρ c).x1Inv =
      (FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf deltaF c (1 : ZMod P)))⁻¹ := rfl
theorem cfi_mv (γ ρ : KQ) (c : CellVals (ZMod P) KQ) : (cellFillInv deltaF γ ρ c).mv = c.mv := rfl
theorem cfi_mx (γ ρ : KQ) (c : CellVals (ZMod P) KQ) : (cellFillInv deltaF γ ρ c).mx = c.mx := rfl
theorem cfi_mx1 (γ ρ : KQ) (c : CellVals (ZMod P) KQ) : (cellFillInv deltaF γ ρ c).mx1 = c.mx1 := rfl

section RBFields
variable (z : KQ) (cs : List Noun) (mv mx : ℕ → ℕ) (pt : Noun → ℕ) (n : Noun) (j : ℕ)

theorem RB_p : (RB z cs mv mx pt n j).p = GlobalCarryRecognizer.enc z n := rfl
theorem RB_l : (RB z cs mv mx pt n j).l = GlobalCarryRecognizer.enc z (hdN' n) := by
  rw [hdN'_eq]; rfl
theorem RB_r : (RB z cs mv mx pt n j).r = GlobalCarryRecognizer.enc z (tlN' n) := by
  rw [tlN'_eq]; rfl
theorem RB_idx : (RB z cs mv mx pt n j).idx = (j : ZMod P) := rfl
theorem RB_lo : (RB z cs mv mx pt n j).lo = ((n.internal % 2 ^ 62 : ℕ) : ZMod P) := rfl
theorem RB_hi : (RB z cs mv mx pt n j).hi = ((n.internal / 2 ^ 62 : ℕ) : ZMod P) := rfl
theorem RB_loR : (RB z cs mv mx pt n j).loR = (((tlN' n).internal % 2 ^ 62 : ℕ) : ZMod P) := by
  rw [tlN'_eq]; rfl
theorem RB_hiR : (RB z cs mv mx pt n j).hiR = (((tlN' n).internal / 2 ^ 62 : ℕ) : ZMod P) := by
  rw [tlN'_eq]; rfl
theorem RB_mv : (RB z cs mv mx pt n j).mv = (mv j : ZMod P) := rfl
theorem RB_mx : (RB z cs mv mx pt n j).mx = (mx j : ZMod P) := rfl
theorem RB_mx1 : (RB z cs mv mx pt n j).mx1 = 0 := by
  show ((0 : ℕ) : ZMod P) = 0; simp
theorem RB_idR_cell (hr : (tlN' n).isCell = true) : (RB z cs mv mx pt n j).idR = (pt n : ZMod P) := by
  have : (tlN n).isCell = true := by rw [← tlN'_eq]; exact hr
  simp [RB, ComplJ8Cell.cellRowBP, ComplJ8Cell.idRP, this]

/-- The honest row's left weight is `0` (the head is a small atom). -/
theorem RB_wL (hn : AtomRow n) : (RB z cs mv mx pt n j).wL = 0 := by
  obtain ⟨a, t, rfl, ha, ht⟩ := hn.shape
  simp [RB, ComplJ8Cell.cellRowBP, ComplJ8Cell.cellRowB, ComplJ8Cell.wOf, ComplJ8Cell.isBig, hdN, Noun.isCell]

theorem RB_wR_cell (hr : (tlN' n).isCell = true) : (RB z cs mv mx pt n j).wR = 1 := by
  have : (tlN n).isCell = true := by rw [← tlN'_eq]; exact hr
  simp [RB, ComplJ8Cell.cellRowBP, ComplJ8Cell.cellRowB, ComplJ8Cell.wOf, this]

theorem RB_wR_atom (hr : (tlN' n).isCell = false) : (RB z cs mv mx pt n j).wR = 0 := by
  have : (tlN n).isCell = false := by rw [← tlN'_eq]; exact hr
  simp [RB, ComplJ8Cell.cellRowBP, ComplJ8Cell.cellRowB, ComplJ8Cell.wOf, ComplJ8Cell.isBig, this]

end RBFields

variable (pt : Noun → ℕ) (k : Co) (y : K6) (cs : List Noun) (mv mx : ℕ → ℕ) (n : Noun) (j : ℕ) (z γ ρ : KQ)
  (hz : K6.toQ k.z = z) (hγ : K6.toQ k.γ = γ) (hρ : K6.toQ k.ρ = ρ) (hn : AtomRow n)

include hz hn in
theorem toQ_pE : (encE k.z y n).toQ = (RB z cs mv mx pt n j).p := by
  obtain ⟨a, t, rfl, ha, ht⟩ := hn.shape
  rw [toQ_encE_small k.z y (.cell (.atom a) t) ⟨ha, ht⟩, hz, RB_p]

include hz hn in
theorem toQ_lE : (encE k.z y (hdN' n)).toQ = (RB z cs mv mx pt n j).l := by
  obtain ⟨a, t, rfl, ha, ht⟩ := hn.shape
  rw [RB_l]
  show (encE k.z y (.atom a)).toQ = _
  rw [toQ_encE_small k.z y (.atom a) ha, hz]
  rfl

include hz hn in
theorem toQ_rE : (encE k.z y (tlN' n)).toQ = (RB z cs mv mx pt n j).r := by
  obtain ⟨a, t, rfl, ha, ht⟩ := hn.shape
  rw [RB_r]
  show (encE k.z y t).toQ = _
  rw [toQ_encE_small k.z y t ht, hz]
  rfl

include hz hn in
theorem toQ_pE_d : (cellDE pt k y cs n j).pE.toQ = (RB z cs mv mx pt n j).p := by
  rw [cellDE_pE]; exact toQ_pE pt k y cs mv mx n j z hz hn

include hz hn in
theorem toQ_lE_d : (cellDE pt k y cs n j).lE.toQ = (RB z cs mv mx pt n j).l := by
  rw [cellDE_lE]; exact toQ_lE pt k y cs mv mx n j z hz hn

include hz hn in
theorem toQ_rE_d : (cellDE pt k y cs n j).rE.toQ = (RB z cs mv mx pt n j).r := by
  rw [cellDE_rE]; exact toQ_rE pt k y cs mv mx n j z hz hn

include hz hγ hρ hn in
theorem toQ_vInv : K6.toQ (cellDE pt k y cs n j).vInv =
    (cellFillInv deltaF γ ρ (RB z cs mv mx pt n j)).vInv := by
  subst hγ hρ
  have hp := toQ_pE pt k y cs mv mx n j z hz hn
  have hlo := RB_lo z cs mv mx pt n j
  have hhi := RB_hi z cs mv mx pt n j
  have hix := RB_idx z cs mv mx pt n j
  generalize RB z cs mv mx pt n j = R at *
  rw [cellDE_vInv, K6.toQ_inv, toQ_compressE, cfi_vInv]
  congr 2
  funext c
  fin_cases c
  · exact congrArg ComputeTable.FP.size hp
  · exact congrArg ComputeTable.FP.dyck hp
  · exact congrArg ComputeTable.FP.leaf hp
  · show K6.toQ (rkK _) = Quad.mk _ (algebraMap _ KC R.lo) (algebraMap _ KC R.hi)
    rw [hlo, hhi]; exact toQ_rkK _
  · show K6.toQ (lq j) = liftQ deltaF R.idx
    rw [hix]; exact toQ_lq j

include hz hγ hρ hn in
theorem toQ_lInv : K6.toQ (cellDE pt k y cs n j).lInv =
    (cellFillInv deltaF γ ρ (RB z cs mv mx pt n j)).lInv := by
  have hl : (hdN' n).isCell = false := by
    obtain ⟨a, t, rfl, -, -⟩ := hn.shape; rfl
  rw [cellDE_lInv pt k y cs n j hl, K6.toQ_zero, cfi_lInv, RB_wL z cs mv mx pt n j hn, liftQ, map_zero, map_zero,
    zero_mul]

include hz hγ hρ hn in
theorem toQ_rInv : K6.toQ (cellDE pt k y cs n j).rInv =
    (cellFillInv deltaF γ ρ (RB z cs mv mx pt n j)).rInv := by
  subst hγ hρ
  by_cases hr : (tlN' n).isCell = true
  · have hrE := toQ_rE pt k y cs mv mx n j z hz hn
    have hlo := RB_loR z cs mv mx pt n j
    have hhi := RB_hiR z cs mv mx pt n j
    have hid := RB_idR_cell z cs mv mx pt n j hr
    have hw := RB_wR_cell z cs mv mx pt n j hr
    generalize RB z cs mv mx pt n j = R at *
    rw [cellDE_rInv_cell pt k y cs n j hr, K6.toQ_inv, toQ_compressE, cfi_rInv, hw, liftQ, map_one, map_one,
      one_mul]
    congr 2
    funext c
    fin_cases c
    · exact congrArg ComputeTable.FP.size hrE
    · exact congrArg ComputeTable.FP.dyck hrE
    · exact congrArg ComputeTable.FP.leaf hrE
    · show K6.toQ (rkK _) = Quad.mk _ (algebraMap _ KC R.loR) (algebraMap _ KC R.hiR)
      rw [hlo, hhi]; exact toQ_rkK _
    · show K6.toQ (lq (pt n)) = liftQ deltaF R.idR
      rw [hid]; exact toQ_lq _
  · have hr' : (tlN' n).isCell = false := by simpa using hr
    rw [cellDE_rInv_atom pt k y cs n j hr', K6.toQ_zero, cfi_rInv, RB_wR_atom z cs mv mx pt n j hr', liftQ,
      map_zero, map_zero, zero_mul]

include hz hγ hρ hn in
theorem toQ_x0Inv : K6.toQ (cellDE pt k y cs n j).x0Inv =
    (cellFillInv deltaF γ ρ (RB z cs mv mx pt n j)).x0Inv := by
  subst hγ hρ
  have hp := toQ_pE pt k y cs mv mx n j z hz hn
  have hl := toQ_lE pt k y cs mv mx n j z hz hn
  have hr := toQ_rE pt k y cs mv mx n j z hz hn
  have hix := RB_idx z cs mv mx pt n j
  generalize RB z cs mv mx pt n j = R at *
  rw [cellDE_x0Inv, K6.toQ_inv, toQ_compressE, cfi_x0Inv]
  congr 2
  funext c
  fin_cases c
  · exact congrArg ComputeTable.FP.size hp
  · exact congrArg ComputeTable.FP.dyck hp
  · exact congrArg ComputeTable.FP.leaf hp
  · exact congrArg ComputeTable.FP.size hl
  · exact congrArg ComputeTable.FP.dyck hl
  · exact congrArg ComputeTable.FP.leaf hl
  · exact congrArg ComputeTable.FP.size hr
  · exact congrArg ComputeTable.FP.dyck hr
  · exact congrArg ComputeTable.FP.leaf hr
  · show K6.toQ (lq j) = liftQ deltaF R.idx
    rw [hix]; exact toQ_lq j
  · show K6.toQ (lq 0) = liftQ deltaF (0 : ZMod P)
    rw [toQ_lq, Nat.cast_zero]

include hz hγ hρ hn in
theorem toQ_x1Inv : K6.toQ (cellDE pt k y cs n j).x1Inv =
    (cellFillInv deltaF γ ρ (RB z cs mv mx pt n j)).x1Inv := by
  subst hγ hρ
  have hp := toQ_pE pt k y cs mv mx n j z hz hn
  have hl := toQ_lE pt k y cs mv mx n j z hz hn
  have hr := toQ_rE pt k y cs mv mx n j z hz hn
  have hix := RB_idx z cs mv mx pt n j
  generalize RB z cs mv mx pt n j = R at *
  rw [cellDE_x1Inv, K6.toQ_inv, toQ_compressE, cfi_x1Inv]
  congr 2
  funext c
  fin_cases c
  · exact congrArg ComputeTable.FP.size hp
  · exact congrArg ComputeTable.FP.dyck hp
  · exact congrArg ComputeTable.FP.leaf hp
  · exact congrArg ComputeTable.FP.size hl
  · exact congrArg ComputeTable.FP.dyck hl
  · exact congrArg ComputeTable.FP.leaf hl
  · exact congrArg ComputeTable.FP.size hr
  · exact congrArg ComputeTable.FP.dyck hr
  · exact congrArg ComputeTable.FP.leaf hr
  · show K6.toQ (lq j) = liftQ deltaF R.idx
    rw [hix]; exact toQ_lq j
  · show K6.toQ (lq 1) = liftQ deltaF (1 : ZMod P)
    rw [toQ_lq, Nat.cast_one]

/-! Row terms. -/

variable (mvX mxX mx1X mhX : Array ℕ)

include hz hγ hρ hn in
theorem toQ_vTermD (hmv : mvX.getD j 0 = mv j) :
    K6.toQ (vTermD mvX (cellDE pt k y cs n j)) =
      vTermOf deltaF (cellFillInv deltaF γ ρ (RB z cs mv mx pt n j)) := by
  have h1 := toQ_vInv pt k y cs mv mx n j z γ ρ hz hγ hρ hn
  have h2 := toQ_lInv pt k y cs mv mx n j z γ ρ hz hγ hρ hn
  have h3 := toQ_rInv pt k y cs mv mx n j z γ ρ hz hγ hρ hn
  have hm := (cfi_mv γ ρ (RB z cs mv mx pt n j)).trans (RB_mv z cs mv mx pt n j)
  unfold vTermD vTermOf
  rw [K6.toQ_sub, K6.toQ_sub, K6.toQ_mul, cellDE_j, hmv, toQ_lq, h1, h2, h3, hm]

include hz hγ hρ hn in
theorem toQ_xTermD (hmx : mxX.getD j 0 = mx j) (hmx1 : mx1X.getD j 0 = 0) :
    K6.toQ (xTermD mxX mx1X (cellDE pt k y cs n j)) =
      xTermOf deltaF (cellFillInv deltaF γ ρ (RB z cs mv mx pt n j)) := by
  have h0 := toQ_x0Inv pt k y cs mv mx n j z γ ρ hz hγ hρ hn
  have h1 := toQ_x1Inv pt k y cs mv mx n j z γ ρ hz hγ hρ hn
  have hm := (cfi_mx γ ρ (RB z cs mv mx pt n j)).trans (RB_mx z cs mv mx pt n j)
  have hm1 := (cfi_mx1 γ ρ (RB z cs mv mx pt n j)).trans (RB_mx1 z cs mv mx pt n j)
  unfold xTermD xTermOf
  rw [K6.toQ_add, K6.toQ_mul, K6.toQ_mul, cellDE_j, hmx, hmx1, toQ_lq, toQ_lq, h0, h1, hm, hm1]
  simp only [Nat.cast_zero]

theorem toQ_hTermD (m : ℕ) (hmh : mhX.getD j 0 = m) :
    K6.toQ (hTermD mhX (cellDE pt k y cs n j)) =
      liftQ (K := KC) deltaF (m : ZMod P) * K6.toQ (cellDE pt k y cs n j).ivH := by
  unfold hTermD
  rw [K6.toQ_mul, cellDE_j, hmh, toQ_lq]

end Row

/-! ## 6. At the generic data `D` -/

section DData
variable {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
  (D : ComplJ8Data.J8Data P Rg fuel s f r)

theorem mvE_ptrP_getD (acsL : List Noun) (rows : Array Nock.Edit.GenX.RowNX) {j : ℕ} (hj : j < acsL.length) :
    (mvE acsL (ComplJ8Data.ptrP P acsL rows)).getD j 0 =
      (acsL.filter fun y => (hdN' y).isCell && idxOf acsL (hdN' y) == j).length +
        (acsL.filter fun y => (tlN' y).isCell && ComplJ8Data.ptrP P acsL rows y == j).length := by
  have := GenPortJ9.mvE_getD acsL rows hj
  rw [GenPortJ9.ptrE_eq'] at this
  exact this

theorem mvE_getD_mvA {j : ℕ} (hj : j < D.acs.length) :
    (mvE D.acs (ComplJ8Data.ptrP P D.acs D.rows)).getD j 0 = ComplJ8Of.mvA D j :=
  mvE_ptrP_getD D.acs D.rows hj

theorem replicate_getD (n j : ℕ) : (Array.replicate n 0).getD j 0 = 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> simp

theorem mh_getD {j : ℕ} (hj : j < D.acs.length) :
    ((Array.range D.acs.length).map fun j => D.mhA.getD j 0 + (D.info.getD j AInfo.z).mhx).getD j 0 =
      ComplJ8Of.mhAF D j := by
  simp [Array.getD_eq_getD_getElem?, hj, ComplJ8Of.mhAF]

end DData

#print axioms toQ_encE_small
#print axioms small_of_acs
#print axioms toQ_pE
#print axioms toQ_vInv
#print axioms toQ_rInv
#print axioms toQ_x0Inv
#print axioms toQ_vTermD
#print axioms toQ_xTermD
#print axioms toQ_hTermD
#print axioms mvE_getD_mvA
#print axioms mh_getD
#print axioms toQ_γHE
#print axioms toQ_ρHE

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomRow
