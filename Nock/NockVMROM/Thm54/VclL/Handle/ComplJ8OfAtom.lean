/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8OfAtom.lean

* §1 the atom walk: validity and handle pole families (`famAWV`, `famAWH`), the handle-denominator split, and
    **`awOK_run`** (absent: `awOK_absent`; present: `awOK_list` under `hwalkA : WalkDepthOK preads`).
  * §2 the atom table: the read-set lemma for the three atom denominators (no public, roles `< 6`, base columns
    `< 205`, chal leaves `11..20 ∪ 37..38` resp. `33..36`), their pubs-independence, the pole families, the rank
    bound from the row binder, and **`atomOK_run`** (via `ComplJ8AW.atomOK_j8`).

  Both theorems are stated at `BOf … (avOf …) fams` for ANY family list `fams` containing this file's families
  (as `ComplJ8Of.cellOK_run`); they are added to `famsOf`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8BigBound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList quadPole ReadsOff)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AWChipOK)

noncomputable section

/-! ## 1. The atom walk -/

section AWPoles
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

theorem chalsAZ_0 (χ : Coins frameJ8 K) : chalsAJ8Z δ χ 0 = χ ⟨0, by decide⟩ := by
  rw [ChalsAZJ8.chalsAJ8Z_of_ne δ χ (by omega) (by omega)]
  unfold ProbJ8.chalsAJ8
  rw [if_neg (by omega), if_neg (by omega)]
  exact chals_0 δ χ

theorem chalsAZ_1 (χ : Coins frameJ8 K) : chalsAJ8Z δ χ 1 = χ ⟨1, by decide⟩ := by
  rw [ChalsAZJ8.chalsAJ8Z_of_ne δ χ (by omega) (by omega)]
  unfold ProbJ8.chalsAJ8
  rw [if_neg (by omega), if_neg (by omega)]
  exact chals_1 δ χ

/-- The atom-table coin `zA` is the limb coin `y = (χ_{Y1}, χ_{Y2})`. -/
theorem zA_eq (χ : Coins frameJ8 K) : zA δ χ = Quad.mk _ (χ cY1) (χ cY2) := ChalsAZJ8.chalsAJ8Z_y δ χ

/-- The honest atom-walk rows with the walk coins read as coordinates `χ₀ χ₁`. -/
abbrev vRow (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) :
    ℕ → WalkVals (ZMod p) K (Quad (algebraMap (ZMod p) K δ)) :=
  walkRow0 δ (Quad.mk _ (χ cY1) (χ cY2)) D.acs D.preads (χ ⟨0, by decide⟩) (χ ⟨1, by decide⟩)

theorem vR_eq (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) :
    ComplJ8Walk.wRowsB δ (chalsAJ8Z δ χ) (zA δ χ) D.acs D.preads = vRow δ D χ := by
  simp only [ComplJ8Walk.wRowsB, chalsAZ_0, chalsAZ_1, zA_eq]

/-- The three atom-walk validity pole-free parts of row `j`. -/
def awVx (D : J8Data p Rg fuel s f r) (j : ℕ) : List (Coins frameJ8 K → Quad (algebraMap (ZMod p) K δ)) :=
  [fun χ => FiniteIO.compress (m := 11) ⟨γV δ χ, 0⟩ (wxKeyV δ (vRow δ D χ j)),
   fun χ => FiniteIO.compress (m := 8) ⟨γV δ χ, 0⟩ (wrecLV δ (vRow δ D χ j)),
   fun χ => FiniteIO.compress (m := 8) ⟨γV δ χ, 0⟩ (wrecRV δ (vRow δ D χ j))]

/-- **The atom-walk validity pole family.** -/
def famAWV (D : J8Data p Rg fuel s f r) : List (BadSpec K) :=
  (List.range (nVOf D)).flatMap fun j => (awVx δ D j).map (quadPole δ WeightsJ8.c5)

theorem famAWV_OK (D : J8Data p Rg fuel s f r) : ∀ e ∈ famAWV δ D (K := K), e.OK := by
  intro e he
  obtain ⟨j, -, he⟩ := List.mem_flatMap.mp he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  refine ComplJ8Bad.quadPole_OK δ _ _ ?_
  simp only [awVx, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · intro χ χ' h
    simp only [γV, vRow, h WeightsJ8.c4 (by decide), h WeightsJ8.c6 (by decide), h cY1 (by decide),
      h cY2 (by decide), h ⟨0, by decide⟩ (by decide), h ⟨1, by decide⟩ (by decide)]

theorem famAWV_good (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K)
    (hg : ∀ e ∈ famAWV δ D (K := K), χ ∉ e.ev) : ∀ j < nVOf D,
      FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩ (wxKeyV δ (vRow δ D χ j)) ≠ 0 ∧
      FiniteIO.compress (m := 8) ⟨γV δ χ, ρV δ χ⟩ (wrecLV δ (vRow δ D χ j)) ≠ 0 ∧
      FiniteIO.compress (m := 8) ⟨γV δ χ, ρV δ χ⟩ (wrecRV δ (vRow δ D χ j)) ≠ 0 := by
  intro j hj
  have hx : ∀ x ∈ awVx δ D j (K := K), Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7) + x χ ≠ 0 := by
    intro x hx
    refine ComplJ8Bad.quadPole_ne_mk δ _ x χ _ (hg _ ?_)
    exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨x, hx, rfl⟩⟩
  simp only [awVx, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · rw [InhabJ8Good.compress_split]; exact h1
  · rw [InhabJ8Good.compress_split]; exact h2
  · rw [InhabJ8Good.compress_split]; exact h3

/-- The honest atom-walk values with coordinate coins. -/
abbrev vValsC (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) :
    Fin (nVOf D) → WalkVals (ZMod p) K (Quad (algebraMap (ZMod p) K δ)) :=
  fun i => walkFill δ (γV δ χ) (ρV δ χ) (vRow δ D χ) i

/-- The three atom-walk handle pole-free parts of row `j`. -/
def awHx (D : J8Data p Rg fuel s f r) (j : ℕ) : List (Coins frameJ8 K → Quad (algebraMap (ZMod p) K δ)) :=
  if hj : j < nVOf D then
    [fun χ => recDen 0 (ComplJ8Bad.γH δ χ) ((vValsC δ D χ ⟨j, hj⟩).idx, (kLV D ⟨j, hj⟩, vLV D ⟨j, hj⟩),
        (kRV D ⟨j, hj⟩, vRV D ⟨j, hj⟩)),
     fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((vValsC δ D χ ⟨j, hj⟩).ridx, 2 * (vValsC δ D χ ⟨j, hj⟩).pre,
        (kLV D ⟨j, hj⟩, vLV D ⟨j, hj⟩)),
     fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((vValsC δ D χ ⟨j, hj⟩).ridx, 2 * (vValsC δ D χ ⟨j, hj⟩).pre + 1,
        (kRV D ⟨j, hj⟩, vRV D ⟨j, hj⟩))]
  else []

/-- **The atom-walk handle pole family.** -/
def famAWH (D : J8Data p Rg fuel s f r) : List (BadSpec K) :=
  (List.range (nVOf D)).flatMap fun j => (awHx δ D j).map (quadPole δ InhabJ8Good.c12)

theorem famAWH_OK (D : J8Data p Rg fuel s f r) : ∀ e ∈ famAWH δ D (K := K), e.OK := by
  intro e he
  obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  refine ComplJ8Bad.quadPole_OK δ _ _ ?_
  have hj' := List.mem_range.mp hj
  simp only [awHx, dif_pos hj', List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · intro χ χ' h
    have hγ : ComplJ8Bad.γH δ χ = ComplJ8Bad.γH δ χ' := ComplJ8Bad.γH_readsOff δ χ χ' h
    simp only [hγ, vValsC, γV, ρV, vRow, h WeightsJ8.c4 (by decide), h WeightsJ8.c5 (by decide),
      h WeightsJ8.c6 (by decide), h WeightsJ8.c7 (by decide), h cY1 (by decide), h cY2 (by decide),
      h ⟨0, by decide⟩ (by decide), h ⟨1, by decide⟩ (by decide)]

theorem vVals_eq (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) :
    ComplJ8Walk.wValsB (n := nVOf D) δ (chalsAJ8Z δ χ) (zA δ χ) (γV δ χ) (ρV δ χ) D.acs D.preads =
      vValsC δ D χ := by
  unfold ComplJ8Walk.wValsB
  rw [vR_eq]

variable (b : Basis (Fin 3) (ZMod p) K)

/-- **The three atom-walk handle denominators split** as `ρH + (pole-free part)` at any publics. -/
theorem aw_dRow_split (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (nVOf D))) (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin (nVOf D)) :
    WalkTraceHQ.dRow δ (krW D.acs D.preads) b (nV_pos D) (powN o _) o (chalsAJ8Z δ χ) pubs
        WalkHC.xKeyH (vCol δ b D χ) (kLV D) (vLV D) (kRV D) (vRV D) i =
      ComplJ8Bad.ρH δ χ + recDen 0 (ComplJ8Bad.γH δ χ) ((vValsC δ D χ i).idx, (kLV D i, vLV D i), (kRV D i, vRV D i)) ∧
    WalkTraceHQ.dRow δ (krW D.acs D.preads) b (nV_pos D) (powN o _) o (chalsAJ8Z δ χ) pubs
        WalkHC.recLH (vCol δ b D χ) (kLV D) (vLV D) (kRV D) (vRV D) i =
      ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) ((vValsC δ D χ i).ridx, 2 * (vValsC δ D χ i).pre,
        (kLV D i, vLV D i)) ∧
    WalkTraceHQ.dRow δ (krW D.acs D.preads) b (nV_pos D) (powN o _) o (chalsAJ8Z δ χ) pubs
        WalkHC.recRH (vCol δ b D χ) (kLV D) (vLV D) (kRV D) (vRV D) i =
      ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) ((vValsC δ D χ i).ridx, 2 * (vValsC δ D χ i).pre + 1,
        (kRV D i, vRV D i)) := by
  obtain ⟨e1, e2, e3⟩ := FrameVSQ.walk_dRowQ_vals δ (krW D.acs D.preads) b (nV_pos D) (powN o _) o
    (chalsAJ8Z δ χ) pubs (ComplJ8Walk.wValsB δ (chalsAJ8Z δ χ) (zA δ χ) (γV δ χ) (ρV δ χ) D.acs D.preads)
    (kLV D) (vLV D) (kRV D) (vRV D) hinj i
  have hρ : Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 34) (chalsAJ8Z δ χ 36) = ComplJ8Bad.ρH δ χ := by
    rw [ChalsAZJ8.chalsAJ8Z_agree δ χ 34 (by norm_num) (by norm_num),
      ChalsAZJ8.chalsAJ8Z_agree δ χ 36 (by norm_num) (by norm_num), chals_34, chals_36]; rfl
  have hγ : Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 33) (chalsAJ8Z δ χ 35) = ComplJ8Bad.γH δ χ := by
    rw [ChalsAZJ8.chalsAJ8Z_agree δ χ 33 (by norm_num) (by norm_num),
      ChalsAZJ8.chalsAJ8Z_agree δ χ 35 (by norm_num) (by norm_num), chals_33, chals_35]; rfl
  rw [hρ, hγ, vVals_eq] at e1 e2 e3
  exact ⟨e1.trans (recDen_split δ _ _ _), e2.trans (recDenP_split δ _ _ _), e3.trans (recDenP_split δ _ _ _)⟩

theorem aw_dN_pubs (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (nVOf D))) (χ : Coins frameJ8 K)
    (pubs pubs' : ℕ → K) (l : List (CoeffExpr (ZMod p))) (hl : l = WalkHC.xKeyH ∨ l = WalkHC.recLH ∨ l = WalkHC.recRH)
    (j : ℕ) :
    WalkTraceHQ.dN δ (krW D.acs D.preads) b (nV_pos D) (powN o _) o (chalsAJ8Z δ χ) pubs
      (vCol δ b D χ) (kLV D) (vLV D) (kRV D) (vRV D) l j =
    WalkTraceHQ.dN δ (krW D.acs D.preads) b (nV_pos D) (powN o _) o (chalsAJ8Z δ χ) pubs'
      (vCol δ b D χ) (kLV D) (vLV D) (kRV D) (vRV D) l j := by
  unfold WalkTraceHQ.dN
  split_ifs with hj
  · have e := aw_dRow_split δ b D o hinj χ pubs ⟨j, hj⟩
    have e' := aw_dRow_split δ b D o hinj χ pubs' ⟨j, hj⟩
    rcases hl with rfl | rfl | rfl
    · rw [e.1, e'.1]
    · rw [e.2.1, e'.2.1]
    · rw [e.2.2, e'.2.2]
  · rfl

end AWPoles

section AWRun
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- **The atom walk at a coin outside its two pole families**, for any run data `D` whose handle kinds are in
`{0, 1, 2}`: absent (`preads = []`) by `awOK_absent`, present by `awOK_list` under `hwalkA`. -/
theorem awOK_D (D : J8Data p Rg fuel s f r) (hF : DvdOK D) (hp63 : 2 ^ 63 < p)
    (h31 : ∀ x ∈ sizesJ8 D, x ≤ 2 ^ 31) (hwalkA : ComplJ8Walk.WalkDepthOK D.preads)
    (hkind : ∀ x, ((D.H x).1 : ZMod p) = 0 ∨ ((D.H x).1 : ZMod p) = 1 ∨ ((D.H x).1 : ZMod p) = 2)
    (χ : Coins frameJ8 K) (hgV : ∀ e ∈ famAWV δ D (K := K), χ ∉ e.ev)
    (hgH : ∀ e ∈ famAWH δ D (K := K), χ ∉ e.ev) :
    AWChipOK δ b (krVOf D) (nV_pos D) (powN (orbJ8 D hF) (nVOf D)) (orbJ8 D hF) (chalsAJ8Z δ χ)
      (pubsVOf δ b D (orbJ8 D hF) χ)
      (fun j => trVOf δ b D (orbJ8 D hF) χ
        (Fin.cast (CellTwinK.walkChipHQK_width δ (krVOf D) b (nV_pos D) _ _ _ _) j)) := by
  by_cases h0 : D.preads = []
  · refine ComplJ8AW.awOK_absent δ b (krVOf D) (nV_pos D) _ _ _ _ (by simp [krVOf, h0]) _ ?_
    simp [pubsVOf, h0]
  have hk : krVOf D = krW D.acs D.preads := by simp [krVOf, h0]
  have hN : nVOf D = (walkRows D.acs D.preads).length := by simp [nVOf, h0]
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hmV : nVOf D ∈ sizesJ8 D := by simp [sizesJ8]
  have hmA : D.acs.length ∈ sizesJ8 D := by simp [sizesJ8]
  obtain ⟨hinj, hadj⟩ := powN_ok (orbJ8 D hF) (le_two_pow_ht D hmV)
  have hcells : D.acs.length < ringChar (ZMod p) := by
    have := h31 _ hmA; have : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
    rw [hrc]; omega
  have hkp : krW D.acs D.preads + (walkRows D.acs D.preads).length < ringChar (ZMod p) := by
    have h1 := h31 _ hmV
    have h2 := krW_le_rows D.acs D.preads
    have : (2 : ℕ) ^ 31 + 2 ^ 31 < 2 ^ 63 := by norm_num
    rw [hrc]; rw [hN] at h1; omega
  have hrows := famAWV_good δ D χ hgV
  have hpoleH : ∀ (i : Fin (nVOf D)), ∀ x ∈ awHx δ D i (K := K), ComplJ8Bad.ρH δ χ + x χ ≠ 0 := by
    intro i x hx
    refine ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12 x χ _ (ComplJ8Bad.ρH_re δ χ) (hgH _ ?_)
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr i.isLt, List.mem_map.mpr ⟨x, hx, rfl⟩⟩
  have hsplit := aw_dRow_split δ b D (orbJ8 D hF) hinj χ (pubsVOf δ b D (orbJ8 D hF) χ)
  have hP : ∀ i, pubsVOf δ b D (orbJ8 D hF) χ i =
      if i < 4 then pubsV0 δ D χ i else if i < 6 then pub2 δ (vhX δ b D (orbJ8 D hF) χ) i
      else if i < 8 then pub2 δ (vhP δ b D (orbJ8 D hF) χ) i else 0 := by
    intro i; simp only [pubsVOf, if_neg h0]
  have hP0 : ∀ i, pubsV0 δ D χ i =
      if i < 2 then pub2 δ (vxT δ D χ) i else if i < 4 then pub2 δ (vpT δ D χ) i else 0 := by
    intro i; simp only [pubsV0, if_neg h0]
  have qx : ∀ i, i < 2 → pubsVOf δ b D (orbJ8 D hF) χ i = pub2 δ (vxT δ D χ) i := by
    intro i hi; rw [hP, if_pos (show i < 4 by omega), hP0, if_pos hi]
  have qp : ∀ i, 2 ≤ i → i < 4 → pubsVOf δ b D (orbJ8 D hF) χ i = pub2 δ (vpT δ D χ) i := by
    intro i h1 h2; rw [hP, if_pos h2, hP0, if_neg (show ¬ i < 2 by omega), if_pos h2]
  have qhx : ∀ i, 4 ≤ i → i < 6 → pubsVOf δ b D (orbJ8 D hF) χ i = pub2 δ (vhX δ b D (orbJ8 D hF) χ) i := by
    intro i h1 h2; rw [hP, if_neg (show ¬ i < 4 by omega), if_pos h2]
  have qhp : ∀ i, 6 ≤ i → i < 8 → pubsVOf δ b D (orbJ8 D hF) χ i = pub2 δ (vhP δ b D (orbJ8 D hF) χ) i := by
    intro i h1 h2; rw [hP, if_neg (show ¬ i < 4 by omega), if_neg (show ¬ i < 6 by omega), if_pos h2]
  have hres := ComplJ8AW.awOK_list δ b (nV_pos D) (powN (orbJ8 D hF) (nVOf D)) (orbJ8 D hF) (chalsAJ8Z δ χ)
    (pubsVOf δ b D (orbJ8 D hF) χ) (zA δ χ) (γV δ χ) (ρV δ χ) D.acs D.preads (kLV D) (vLV D) (kRV D) (vRV D)
    (by rw [hrc]; exact hp63) hcells hwalkA hkp hN hinj hadj (ChalsAZJ8.chalsAJ8Z_ok δ χ)
    (fun j hj => by rw [vR_eq]; exact (hrows j hj).1) (fun j hj => by rw [vR_eq]; exact (hrows j hj).2.1)
    (fun j hj => by rw [vR_eq]; exact (hrows j hj).2.2)
    (by
      rw [qx 0 (by norm_num), qx 1 (by norm_num), pub2_mk2 δ _ 0 rfl]
      rfl)
    (by
      rw [qp 2 (by norm_num) (by norm_num), qp 3 (by norm_num) (by norm_num), pub2_mk2 δ _ 2 rfl]
      rfl)
    (fun i => hkind _) (fun i => hkind _)
    (fun i => by
      rw [(hsplit i).1]
      exact hpoleH i (fun χ => recDen 0 (ComplJ8Bad.γH δ χ) ((vValsC δ D χ i).idx, (kLV D i, vLV D i),
        (kRV D i, vRV D i))) (by simp only [awHx, dif_pos i.isLt]; exact List.mem_cons_self))
    (fun i => by
      rw [(hsplit i).2.1]
      exact hpoleH i (fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((vValsC δ D χ i).ridx, 2 * (vValsC δ D χ i).pre,
        (kLV D i, vLV D i))) (by simp only [awHx, dif_pos i.isLt]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    (fun i => by
      rw [(hsplit i).2.2]
      exact hpoleH i (fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((vValsC δ D χ i).ridx, 2 * (vValsC δ D χ i).pre + 1,
        (kRV D i, vRV D i))) (by
          simp only [awHx, dif_pos i.isLt]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (by
      show Quad.mk _ (pubsVOf δ b D (orbJ8 D hF) χ 4) (pubsVOf δ b D (orbJ8 D hF) χ 5) = _
      rw [qhx 4 (by norm_num) (by norm_num), qhx 5 (by norm_num) (by norm_num), pub2_mk2 δ _ 4 rfl]
      unfold vhX
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold vdN
      rw [hk, aw_dN_pubs δ b D (orbJ8 D hF) hinj χ (pubsV0 δ D χ) (pubsVOf δ b D (orbJ8 D hF) χ) _ (Or.inl rfl)])
    (by
      show Quad.mk _ (pubsVOf δ b D (orbJ8 D hF) χ 6) (pubsVOf δ b D (orbJ8 D hF) χ 7) = _
      rw [qhp 6 (by norm_num) (by norm_num), qhp 7 (by norm_num) (by norm_num), pub2_mk2 δ _ 6 rfl]
      unfold vhP
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold vdN
      rw [hk, aw_dN_pubs δ b D (orbJ8 D hF) hinj χ (pubsV0 δ D χ) (pubsVOf δ b D (orbJ8 D hF) χ) _
          (Or.inr (Or.inl rfl)),
        aw_dN_pubs δ b D (orbJ8 D hF) hinj χ (pubsV0 δ D χ) (pubsVOf δ b D (orbJ8 D hF) χ) _ (Or.inr (Or.inr rfl))])
  unfold trVOf
  rw [hk]
  exact hres

end AWRun

section AWAtRun
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **`awOK` at the run** (the `OpenJ8.awOK` field at `BOf … (avOf …) fams`), given the two atom-walk pole families
are in `fams`; binder `hwalkA := WalkDepthOK preads`. -/
theorem awOK_run (hF : DvdOK (j8DataOf p Rg Rt hgen)) (hC : 0 < (j8DataOf p Rg Rt hgen).cells.length)
    (hA : 0 < (j8DataOf p Rg Rt hgen).acs.length) (fams : List (List (BadSpec K)))
    (hp63 : 2 ^ 63 < p) (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads)
    (hV : famAWV δ (j8DataOf p Rg Rt hgen) ∈ fams) (hH : famAWH δ (j8DataOf p Rg Rt hgen) ∈ fams)
    (χ : Coins frameJ8 K)
    (hχ : (BOf δ b Rt hgen hF hC hA (avOf δ b (j8DataOf p Rg Rt hgen) hF hA) fams).Good χ) :
    let B := BOf δ b Rt hgen hF hC hA (avOf δ b (j8DataOf p Rg Rt hgen) hF hA) fams
    AWChipOK δ b B.Pb.krootsV B.Pb.hnV B.Pb.nodesV B.Pb.orbitV (chalsAJ8Z δ χ) (B.M χ).pubsV
      (AcceptsJ8.qV δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsV) := by
  intro B
  have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(j8DataOf p Rg Rt hgen).t]).length)] fams),
      χ ∉ e.1 := hχ
  have hin : ∀ L ∈ fams, ∀ e ∈ L, χ ∉ e.ev := fun L hL e he =>
    ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨L, hL, he⟩))
  exact awOK_D δ b (j8DataOf p Rg Rt hgen) hF hp63 h31 hwalkA (fun x => hdl_kind _ _ _) χ (hin _ hV) (hin _ hH)

end AWAtRun

/-! ## 2. The atom table -/

section AtomDen
open Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- The atom table's zero-role-fill row environment (base field), at publics `pubs`. -/
abbrev ezA (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) : Env (ZMod p) :=
  HonestA8.EZ δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs (colAH δ b D hA o χ pubs) (newBA D) i

/-- Its gathered `𝕂` environment. -/
abbrev ekA (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) : Env K :=
  gatherEnv b ((AtomChipHQ.atomTemplateHQ δ).col0 3) (ezA δ b D hA o χ pubs i)

theorem ekA_chal (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) :
    (ekA δ b D hA o χ pubs i).chal = chalsAJ8Z δ χ := by
  funext r
  simp only [ekA, ezA, HonestA8.EZ, gatherEnv, ChipTemplate.col0, AtomChipHQ.atomTemplateHQ_baseCols,
    Reify.envOfTrace]
  exact sum_slotVal b 205 r _

/-- The cell part's columns below `184` read only `zA` (the cell part's fingerprint seed). -/
theorem colAH_cong (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ χ' : Coins frameJ8 K) (pubs pubs' : ℕ → K) (hz : zA δ χ = zA δ χ')
    (k : ℕ) (hk : k < 184) : colAH δ b D hA o χ pubs k = colAH δ b D hA o χ' pubs' k :=
  InhabJ8Stage.colHQ_cong δ b _ _ _ _ _ _ _ k hk (fun h => aCol_cong δ b D χ χ' k (by omega) (fun _ => hz))
    (fun h => aCol_cong δ b D χ χ' (k - 1) (by omega) (fun _ => hz))

/-- **The atom row environment's base columns `< 223`** (cell part `< 130`, the added columns, the cell part's
roles `0..5`) read only `zA`: no public, no other coin. -/
theorem ezA_trace (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ χ' : Coins frameJ8 K) (pubs pubs' : ℕ → K) (hz : zA δ χ = zA δ χ')
    (i : Fin D.acs.length) : ∀ j < 223,
      (ezA δ b D hA o χ pubs i).trace j = (ezA δ b D hA o χ' pubs' i).trace j ∧
      (ezA δ b D hA o χ pubs i).traceNext j = (ezA δ b D hA o χ' pubs' i).traceNext j := by
  intro j hj
  have hw : j < (AtomChipHQ.atomTemplateHQ δ).width 3 := by rw [HonestA8.atomTemplateHQ_width]; omega
  have hW : (cellTemplateHQ δ).width 3 = 238 := CellTraceHQ.cellTemplateHQ_width δ
  have hcol : HonestA8.colZ δ (colAH δ b D hA o χ pubs) (newBA D) j =
      HonestA8.colZ δ (colAH δ b D hA o χ' pubs') (newBA D) j := by
    funext i'
    simp only [HonestA8.colZ, extColF, hW]
    split_ifs with h1 h2 h3
    · rw [colAH_cong δ b D hA o χ χ' pubs pubs' hz j (by omega)]
    · rfl
    · rw [colAH_cong δ b D hA o χ χ' pubs pubs' hz (j - (205 - 130)) (by omega)]
    · rfl
  have hq := honestQ_congr hA (powN o _) _ _ ((AtomChipHQ.atomTemplateHQ δ).width 3) ⟨j, hw⟩ hcol
  simp [ezA, HonestA8.EZ, Reify.envOfTrace, dif_pos hw, hq]

theorem ekA_trace (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ χ' : Coins frameJ8 K) (pubs pubs' : ℕ → K) (hz : zA δ χ = zA δ χ')
    (i : Fin D.acs.length) : ∀ r < 6,
      (ekA δ b D hA o χ pubs i).trace r = (ekA δ b D hA o χ' pubs' i).trace r ∧
      (ekA δ b D hA o χ pubs i).traceNext r = (ekA δ b D hA o χ' pubs' i).traceNext r := by
  intro r hr
  have e := fun k : Fin 3 => ezA_trace δ b D hA o χ χ' pubs pubs' hz i (205 + 3 * r + k) (by omega)
  simp only [ekA, gatherEnv, ChipTemplate.col0, AtomChipHQ.atomTemplateHQ_baseCols]
  exact ⟨Finset.sum_congr rfl fun k _ => by rw [(e k).1], Finset.sum_congr rfl fun k _ => by rw [(e k).2]⟩

/-- `mbKey`'s entries read the coin leaves `37 38`, the roles `4 5` and the base column `idx`. -/
theorem keyVec_mb_congr (eK eK' : Env K) (eF eF' : Env (ZMod p)) (h37 : eK.chal 37 = eK'.chal 37)
    (h38 : eK.chal 38 = eK'.chal 38) (h4 : eK.trace 4 = eK'.trace 4) (h5 : eK.trace 5 = eK'.trace 5)
    (h2 : eF.trace 2 = eF'.trace 2) :
    keyVec δ 5 (AtomChipHQ.mbKey (F := ZMod p)) eK eF = keyVec δ 5 AtomChipHQ.mbKey eK' eF' := by
  funext c
  fin_cases c <;>
    simp [keyVec, AtomChipHQ.mbKey, AtomChipHQ.zAt, QE.ev, QE.chal, QE.var, QE.zero, QE.base, MixedExpr.eval,
      CoeffExpr.eval, cv, Cell.pR, Cell.idx, h37, h38, h4, h5, h2]

theorem keyVec5_congr (B : ℕ) (l : List (CoeffExpr (ZMod p)))
    (hl : ∀ c : Fin 5, colsBelow B (l.getD c (.const 0)) = true) (e e' : Env (ZMod p))
    (ht : ∀ j < B, e.trace j = e'.trace j) (hn : ∀ j < B, e.traceNext j = e'.traceNext j) :
    ServeH.keyVec5 (K := K) l e = ServeH.keyVec5 l e' := by
  funext c
  simp only [ServeH.keyVec5]
  rw [colsBelow_eval (hl c) ht hn]

theorem oldKey_below : ∀ c : Fin 5, colsBelow 205 ((AtomChipHQ.oldKey (F := ZMod p)).getD c (.const 0)) = true := by
  intro c; fin_cases c <;> rfl

theorem incKey_below : ∀ c : Fin 5, colsBelow 205 ((AtomChipHQ.incKey (F := ZMod p)).getD c (.const 0)) = true := by
  intro c; fin_cases c <;> rfl

theorem keyH_below : ∀ c : Fin 5, colsBelow 130 ((CellH.keyH (F := ZMod p)).getD c (.const 0)) = true := by
  intro c; fin_cases c <;> rfl

/-- The atom chip's handle coins are the handle coins `γH ρH`. -/
theorem coinsQ_ekA (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) :
    TeleHQ.coinsQ δ (ekA δ b D hA o χ pubs i) = ⟨ComplJ8Bad.γH δ χ, ComplJ8Bad.ρH δ χ⟩ := by
  unfold TeleHQ.coinsQ
  rw [ekA_chal, ChalsAZJ8.chalsAJ8Z_agree δ χ 33 (by norm_num) (by norm_num),
    ChalsAZJ8.chalsAJ8Z_agree δ χ 35 (by norm_num) (by norm_num),
    ChalsAZJ8.chalsAJ8Z_agree δ χ 34 (by norm_num) (by norm_num),
    ChalsAZJ8.chalsAJ8Z_agree δ χ 36 (by norm_num) (by norm_num), chals_33, chals_35, chals_34, chals_36]
  rfl

/-- **The read-set lemma for `dMB`**: `dMB = ρ′ + compress (γ′, 0) (z, 0, role 4, 0, idx)` — it reads the
validity coins, the seed leaves `37 38`, the cell part's role `4` (the fingerprint leaf) and base column `idx`;
no public. -/
theorem dMB_eq (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) :
    HonestA8.dMB δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs (colAH δ b D hA o χ pubs) (newBA D) i =
      ρV δ χ + FiniteIO.compress (m := 5) ⟨γV δ χ, 0⟩
        (keyVec δ 5 AtomChipHQ.mbKey (ekA δ b D hA o χ pubs i) (ezA δ b D hA o χ pubs i)) := by
  have hok : ChalsOK δ (ekA δ b D hA o χ pubs i).chal (γV δ χ) (ρV δ χ) (AtomChipHQ.mbKey (F := ZMod p)).length := by
    rw [ekA_chal]
    obtain ⟨h1, h2⟩ := ChalsAZJ8.chalsAJ8Z_ok δ χ
    exact ⟨h1, fun j hj => h2 j (by simp [AtomChipHQ.mbKey] at hj; omega)⟩
  unfold HonestA8.dMB
  rw [den_ev_compress δ _ _ _ _ _ hok, InhabJ8Good.compress_split]
  rfl

/-- **The read-set lemma for `dC`**: `dC = ρH + compress (γH, 0) (keyVec5 oldKey)`; `oldKey` reads base columns
`200 .. 203` only. -/
theorem dC_eq (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) :
    HonestA8.dC δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs (colAH δ b D hA o χ pubs) (newBA D) i =
      ComplJ8Bad.ρH δ χ + FiniteIO.compress (⟨ComplJ8Bad.γH δ χ, 0⟩ : FiniteIO.IOCoins (Quad (algebraMap (ZMod p) K δ)))
        (BalanceQ.liftRec (K := K) (L := Quad (algebraMap (ZMod p) K δ))
          (ServeH.keyVec5 AtomChipHQ.oldKey (ezA δ b D hA o χ pubs i))) := by
  unfold HonestA8.dC
  rw [TeleHQ.denKeyQ_ev δ _ _ _ rfl]
  rw [show gatherEnv b ((AtomChipHQ.atomTemplateHQ δ).col0 3) (HonestA8.EZ δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs
      (colAH δ b D hA o χ pubs) (newBA D) i) = ekA δ b D hA o χ pubs i from rfl, coinsQ_ekA,
    InhabJ8Good.compress_split]

/-- **The read-set lemma for `dMI`**: `dMI = ρH + compress (γH, 0) (keyVec5 incKey)`; `incKey` reads base columns
`conv`, `idx_o`, `idx` only. -/
theorem dMI_eq (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) :
    HonestA8.dMI δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs (colAH δ b D hA o χ pubs) (newBA D) i =
      ComplJ8Bad.ρH δ χ + FiniteIO.compress (⟨ComplJ8Bad.γH δ χ, 0⟩ : FiniteIO.IOCoins (Quad (algebraMap (ZMod p) K δ)))
        (BalanceQ.liftRec (K := K) (L := Quad (algebraMap (ZMod p) K δ))
          (ServeH.keyVec5 AtomChipHQ.incKey (ezA δ b D hA o χ pubs i))) := by
  unfold HonestA8.dMI
  rw [TeleHQ.denKeyQ_ev δ _ _ _ rfl]
  rw [show gatherEnv b ((AtomChipHQ.atomTemplateHQ δ).col0 3) (HonestA8.EZ δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs
      (colAH δ b D hA o χ pubs) (newBA D) i) = ekA δ b D hA o χ pubs i from rfl, coinsQ_ekA,
    InhabJ8Good.compress_split]

end AtomDen

/-! ### Pubs-independence -/

section AtomPubs
open Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- The cell part's handle denominator does not read the publics. -/
theorem dRowHQ_pubs0 {n h : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (chals pubs : ℕ → K) (col : ℕ → Fin n → ZMod p) (mhv : Fin n → ZMod p) (i : Fin n) :
    CellTraceHQ.dRow δ b hn nodes orbit chals pubs col mhv i =
      CellTraceHQ.dRow δ b hn nodes orbit chals (fun _ => 0) col mhv i := by
  unfold CellTraceHQ.dRow
  exact CellTraceHQ.denKeyQ_congr δ b chals _ _ rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)

theorem dNHQ_pubs0 {n h : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (chals pubs : ℕ → K) (col : ℕ → Fin n → ZMod p) (mhv : Fin n → ZMod p) (j : ℕ) :
    CellTraceHQ.dN δ b hn nodes orbit chals pubs col mhv j =
      CellTraceHQ.dN δ b hn nodes orbit chals (fun _ => 0) col mhv j := by
  unfold CellTraceHQ.dN
  split_ifs with hj
  · exact dRowHQ_pubs0 δ b hn nodes orbit chals pubs col mhv _
  · rfl

/-- **The atom table's 238-column cell part does not depend on the publics.** -/
theorem colAH_pubs0 (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) (pubs : ℕ → K) :
    colAH δ b D hA o χ pubs = colAH δ b D hA o χ (fun _ => 0) := by
  unfold colAH
  have h1 : CellTraceHQ.ivF δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs (aCol δ b D χ) (mhvA D) =
      CellTraceHQ.ivF δ b hA (powN o _) o (chalsAJ8Z δ χ) (fun _ => 0) (aCol δ b D χ) (mhvA D) := by
    funext i; simp only [CellTraceHQ.ivF]; rw [dRowHQ_pubs0]
  have h2 : CellTraceHQ.avF δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs (aCol δ b D χ) (mhvA D) =
      CellTraceHQ.avF δ b hA (powN o _) o (chalsAJ8Z δ χ) (fun _ => 0) (aCol δ b D χ) (mhvA D) := by
    funext i; simp only [CellTraceHQ.avF]
    exact Finset.sum_congr rfl fun j _ => by rw [dNHQ_pubs0]
  rw [h1, h2]

/-- **`dMB`, `dC`, `dMI` do not depend on the publics** (neither directly nor through the cell part). -/
theorem dMB_pubs0 (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) :
    HonestA8.dMB δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs (colAH δ b D hA o χ pubs) (newBA D) i =
      HonestA8.dMB δ b hA (powN o _) o (chalsAJ8Z δ χ) (fun _ => 0) (colAH δ b D hA o χ (fun _ => 0)) (newBA D) i := by
  rw [dMB_eq, dMB_eq, keyVec_mb_congr δ (ekA δ b D hA o χ pubs i) (ekA δ b D hA o χ (fun _ => 0) i)
    (ezA δ b D hA o χ pubs i) (ezA δ b D hA o χ (fun _ => 0) i) (by rw [ekA_chal, ekA_chal])
    (by rw [ekA_chal, ekA_chal])
    (ekA_trace δ b D hA o χ χ pubs _ rfl i 4 (by norm_num)).1 (ekA_trace δ b D hA o χ χ pubs _ rfl i 5 (by norm_num)).1
    (ezA_trace δ b D hA o χ χ pubs _ rfl i 2 (by norm_num)).1]

theorem dC_pubs0 (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) :
    HonestA8.dC δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs (colAH δ b D hA o χ pubs) (newBA D) i =
      HonestA8.dC δ b hA (powN o _) o (chalsAJ8Z δ χ) (fun _ => 0) (colAH δ b D hA o χ (fun _ => 0)) (newBA D) i := by
  rw [dC_eq, dC_eq, keyVec5_congr 205 _ oldKey_below _ _
    (fun j hj => (ezA_trace δ b D hA o χ χ pubs _ rfl i j (by omega)).1)
    (fun j hj => (ezA_trace δ b D hA o χ χ pubs _ rfl i j (by omega)).2)]

theorem dMI_pubs0 (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) :
    HonestA8.dMI δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs (colAH δ b D hA o χ pubs) (newBA D) i =
      HonestA8.dMI δ b hA (powN o _) o (chalsAJ8Z δ χ) (fun _ => 0) (colAH δ b D hA o χ (fun _ => 0)) (newBA D) i := by
  rw [dMI_eq, dMI_eq, keyVec5_congr 205 _ incKey_below _ _
    (fun j hj => (ezA_trace δ b D hA o χ χ pubs _ rfl i j (by omega)).1)
    (fun j hj => (ezA_trace δ b D hA o χ χ pubs _ rfl i j (by omega)).2)]

/-! ### The cell part's handle denominator split -/

/-- The coin-free environment of atom cell row `i`. -/
abbrev aE0 (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) (i : Fin D.acs.length) : Env (ZMod p) :=
  CellTraceHQ.E δ b hA (powN o _) o (fun _ => (0 : K)) (fun _ => (0 : K)) (aCol δ b D χ) (mhvA D)
    (fun _ => 0) (fun _ => 0) i

/-- The pole-free part of atom cell row `j`'s handle denominator. -/
def aHx (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (j : ℕ) (χ : Coins frameJ8 K) : Quad (algebraMap (ZMod p) K δ) :=
  if hj : j < D.acs.length then
    FiniteIO.compress (⟨ComplJ8Bad.γH δ χ, 0⟩ : FiniteIO.IOCoins (Quad (algebraMap (ZMod p) K δ)))
      (BalanceQ.liftRec (K := K) (L := Quad (algebraMap (ZMod p) K δ))
        (ServeH.keyVec5 CellH.keyH (aE0 δ b D hA o χ ⟨j, hj⟩)))
  else 0

theorem aRow_split (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) :
    CellTraceHQ.dRow δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs (aCol δ b D χ) (mhvA D) i =
      ComplJ8Bad.ρH δ χ + aHx δ b D hA o i χ := by
  unfold CellTraceHQ.dRow
  rw [TeleHQ.denKeyQ_ev δ _ _ _ rfl]
  have hc : TeleHQ.coinsQ δ (gatherEnv b ((cellTemplateHQ δ).col0 3) (CellTraceHQ.E δ b hA (powN o _) o
      (chalsAJ8Z δ χ) pubs (aCol δ b D χ) (mhvA D) (fun _ => 0) (fun _ => 0) i)) =
      ⟨ComplJ8Bad.γH δ χ, ComplJ8Bad.ρH δ χ⟩ := by
    unfold TeleHQ.coinsQ
    simp only [CellTraceHQ.gather_chal δ b (chalsAJ8Z δ χ) (CellTraceHQ.E δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs
      (aCol δ b D χ) (mhvA D) (fun _ => 0) (fun _ => 0) i) rfl]
    rw [ChalsAZJ8.chalsAJ8Z_agree δ χ 33 (by norm_num) (by norm_num),
      ChalsAZJ8.chalsAJ8Z_agree δ χ 35 (by norm_num) (by norm_num),
      ChalsAZJ8.chalsAJ8Z_agree δ χ 34 (by norm_num) (by norm_num),
      ChalsAZJ8.chalsAJ8Z_agree δ χ 36 (by norm_num) (by norm_num), chals_33, chals_35, chals_34, chals_36]
    rfl
  rw [hc, InhabJ8Good.compress_split]
  simp only [aHx, dif_pos i.isLt, Fin.eta]
  rw [keyVec5_congr 130 _ keyH_below (CellTraceHQ.E δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs (aCol δ b D χ) (mhvA D)
    (fun _ => 0) (fun _ => 0) i) (aE0 δ b D hA o χ i) (fun _ _ => rfl) (fun _ _ => rfl)]

theorem aE0_trace (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ χ' : Coins frameJ8 K) (i : Fin D.acs.length) : ∀ j < 130,
      (aE0 δ b D hA o χ i).trace j = (aE0 δ b D hA o χ' i).trace j ∧
      (aE0 δ b D hA o χ i).traceNext j = (aE0 δ b D hA o χ' i).traceNext j := by
  intro j hj
  have hw : j < (cellTemplateHQ δ).width 3 := by rw [CellTraceHQ.cellTemplateHQ_width]; omega
  have hcol := InhabJ8Stage.colHQ_cong δ b (aCol δ b D χ) (aCol δ b D χ') (mhvA D) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => 0) j (by omega) (fun h => aCol_cong δ b D χ χ' j (by omega) (fun h' => absurd h' (by omega)))
    (fun h => absurd h (by omega))
  have hq := honestQ_congr hA (powN o _) _ _ ((cellTemplateHQ δ).width 3) ⟨j, hw⟩ hcol
  simp [aE0, CellTraceHQ.E, Reify.envOfTrace, dif_pos hw, hq]

end AtomPubs

/-! ### The atom table's pole families -/

section AtomFams
open Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

theorem chalsAZ_37 (χ : Coins frameJ8 K) : chalsAJ8Z δ χ 37 = χ WeightsJ8.c2 := by
  simp [chalsAJ8Z]
theorem chalsAZ_38 (χ : Coins frameJ8 K) : chalsAJ8Z δ χ 38 = χ WeightsJ8.c3 := by
  simp [chalsAJ8Z]

theorem zA_c5 (χ χ' : Coins frameJ8 K) (h : ∀ k, k ≠ WeightsJ8.c5 → χ k = χ' k) : zA δ χ = zA δ χ' := by
  rw [zA_eq, zA_eq, h cY1 (by decide), h cY2 (by decide)]
theorem zA_c12 (χ χ' : Coins frameJ8 K) (h : ∀ k, k ≠ InhabJ8Good.c12 → χ k = χ' k) : zA δ χ = zA δ χ' := by
  rw [zA_eq, zA_eq, h cY1 (by decide), h cY2 (by decide)]

/-- **The atom cell part's seed is non-zero** outside `χ_{Y1} = 0`. -/
def famAZ : List (BadSpec K) := [ComplJ8Bad.zeroEv cY1]

theorem famAZ_OK : ∀ e ∈ famAZ (K := K), e.OK := by
  intro e he; simp only [famAZ, List.mem_singleton] at he; subst he; exact ComplJ8Bad.zeroEv_OK _

theorem famAZ_good (χ : Coins frameJ8 K) (hg : ∀ e ∈ famAZ (K := K), χ ∉ e.ev) : zA δ χ ≠ 0 := by
  have h0 := hg _ (List.mem_singleton_self _)
  simp only [ComplJ8Bad.zeroEv, ComplJ8Bad.BadSpec.ev, Finset.mem_filter, Finset.mem_univ, true_and] at h0
  intro hz
  rw [zA_eq] at hz
  exact h0 ((Quad.mk_eq_zero_iff _ _ _).mp hz).1

/-- The five validity pole-free parts of atom cell row `j`. -/
def aVx (D : J8Data p Rg fuel s f r) (j : ℕ) : List (Coins frameJ8 K → Quad (algebraMap (ZMod p) K δ)) :=
  [fun χ => FiniteIO.compress (m := 5) ⟨γV δ χ, 0⟩ (vKeyOf δ (aRows δ D χ j)),
   fun χ => FiniteIO.compress (m := 5) ⟨γV δ χ, 0⟩ (lKeyOf δ (aRows δ D χ j)),
   fun χ => FiniteIO.compress (m := 5) ⟨γV δ χ, 0⟩ (rKeyOf δ (aRows δ D χ j)),
   fun χ => FiniteIO.compress (m := 11) ⟨γV δ χ, 0⟩ (xKeyOf δ (aRows δ D χ j) 0),
   fun χ => FiniteIO.compress (m := 11) ⟨γV δ χ, 0⟩ (xKeyOf δ (aRows δ D χ j) 1)]

/-- **The atom cell part's validity pole family.** -/
def famAV (D : J8Data p Rg fuel s f r) : List (BadSpec K) :=
  (List.range D.acs.length).flatMap fun j => (aVx δ D j).map (quadPole δ WeightsJ8.c5)

theorem famAV_OK (D : J8Data p Rg fuel s f r) : ∀ e ∈ famAV δ D (K := K), e.OK := by
  intro e he
  obtain ⟨j, -, he⟩ := List.mem_flatMap.mp he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  refine ComplJ8Bad.quadPole_OK δ _ _ ?_
  simp only [aVx, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · intro χ χ' h
    simp only [γV, aRows, zA_c5 δ χ χ' h, h WeightsJ8.c4 (by decide), h WeightsJ8.c6 (by decide)]

theorem famAV_good (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K)
    (hg : ∀ e ∈ famAV δ D (K := K), χ ∉ e.ev) : ∀ j < D.acs.length,
      FiniteIO.compress (m := 5) ⟨γV δ χ, ρV δ χ⟩ (vKeyOf δ (aRows δ D χ j)) ≠ 0 ∧
      FiniteIO.compress (m := 5) ⟨γV δ χ, ρV δ χ⟩ (lKeyOf δ (aRows δ D χ j)) ≠ 0 ∧
      FiniteIO.compress (m := 5) ⟨γV δ χ, ρV δ χ⟩ (rKeyOf δ (aRows δ D χ j)) ≠ 0 ∧
      FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩ (xKeyOf δ (aRows δ D χ j) 0) ≠ 0 ∧
      FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩ (xKeyOf δ (aRows δ D χ j) 1) ≠ 0 := by
  intro j hj
  have hx : ∀ x ∈ aVx δ D j (K := K), Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7) + x χ ≠ 0 := by
    intro x hx
    refine ComplJ8Bad.quadPole_ne_mk δ _ x χ _ (hg _ ?_)
    exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨x, hx, rfl⟩⟩
  simp only [aVx, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [InhabJ8Good.compress_split]; exact h1
  · rw [InhabJ8Good.compress_split]; exact h2
  · rw [InhabJ8Good.compress_split]; exact h3
  · rw [InhabJ8Good.compress_split]; exact h4
  · rw [InhabJ8Good.compress_split]; exact h5

/-- **The atom cell part's handle pole family.** -/
def famAH (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) :
    List (BadSpec K) :=
  (List.range D.acs.length).map fun j => quadPole δ InhabJ8Good.c12 (aHx δ b D hA o j)

theorem famAH_OK (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) : ∀ e ∈ famAH δ b D hA o (K := K), e.OK := by
  intro e he
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp he
  refine ComplJ8Bad.quadPole_OK δ _ _ fun χ χ' hχ => ?_
  unfold aHx
  split_ifs with hj
  · rw [ComplJ8Bad.γH_readsOff δ χ χ' hχ, keyVec5_congr 130 _ keyH_below (aE0 δ b D hA o χ ⟨j, hj⟩)
      (aE0 δ b D hA o χ' ⟨j, hj⟩) (fun k hk => (aE0_trace δ b D hA o χ χ' _ k hk).1)
      (fun k hk => (aE0_trace δ b D hA o χ χ' _ k hk).2)]
  · rfl

/-- The pole-free part of `dMB` at atom row `j`. -/
def mbX (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (j : ℕ) (χ : Coins frameJ8 K) : Quad (algebraMap (ZMod p) K δ) :=
  if hj : j < D.acs.length then
    FiniteIO.compress (m := 5) ⟨γV δ χ, 0⟩ (keyVec δ 5 AtomChipHQ.mbKey
      (ekA δ b D hA o χ (pubsAOf δ b D hA o χ) ⟨j, hj⟩) (ezA δ b D hA o χ (pubsAOf δ b D hA o χ) ⟨j, hj⟩))
  else 0

/-- The pole-free part of `dC` at atom row `j`. -/
def cX (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (j : ℕ) (χ : Coins frameJ8 K) : Quad (algebraMap (ZMod p) K δ) :=
  if hj : j < D.acs.length then
    FiniteIO.compress (⟨ComplJ8Bad.γH δ χ, 0⟩ : FiniteIO.IOCoins (Quad (algebraMap (ZMod p) K δ)))
      (BalanceQ.liftRec (K := K) (L := Quad (algebraMap (ZMod p) K δ))
        (ServeH.keyVec5 AtomChipHQ.oldKey (ezA δ b D hA o χ (pubsAOf δ b D hA o χ) ⟨j, hj⟩)))
  else 0

/-- The pole-free part of `dMI` at atom row `j`. -/
def miX (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (j : ℕ) (χ : Coins frameJ8 K) : Quad (algebraMap (ZMod p) K δ) :=
  if hj : j < D.acs.length then
    FiniteIO.compress (⟨ComplJ8Bad.γH δ χ, 0⟩ : FiniteIO.IOCoins (Quad (algebraMap (ZMod p) K δ)))
      (BalanceQ.liftRec (K := K) (L := Quad (algebraMap (ZMod p) K δ))
        (ServeH.keyVec5 AtomChipHQ.incKey (ezA δ b D hA o χ (pubsAOf δ b D hA o χ) ⟨j, hj⟩)))
  else 0

/-- **The `dMB` pole family** (pole `ρ′`, real part `χ₅`). -/
def famMB (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) :
    List (BadSpec K) :=
  (List.range D.acs.length).map fun j => quadPole δ WeightsJ8.c5 (mbX δ b D hA o j)

/-- **The `dC` pole family** (pole `ρH`, real part `χ₁₂`). -/
def famC (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) :
    List (BadSpec K) :=
  (List.range D.acs.length).map fun j => quadPole δ InhabJ8Good.c12 (cX δ b D hA o j)

/-- **The `dMI` pole family** (pole `ρH`, real part `χ₁₂`). -/
def famMI (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) :
    List (BadSpec K) :=
  (List.range D.acs.length).map fun j => quadPole δ InhabJ8Good.c12 (miX δ b D hA o j)

theorem famMB_OK (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) : ∀ e ∈ famMB δ b D hA o (K := K), e.OK := by
  intro e he
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp he
  refine ComplJ8Bad.quadPole_OK δ _ _ fun χ χ' hχ => ?_
  unfold mbX
  split_ifs with hj
  · have hz := zA_c5 δ χ χ' hχ
    have hγ : γV δ χ = γV δ χ' := by simp only [γV, hχ WeightsJ8.c4 (by decide), hχ WeightsJ8.c6 (by decide)]
    rw [hγ, keyVec_mb_congr δ (ekA δ b D hA o χ (pubsAOf δ b D hA o χ) ⟨j, hj⟩)
      (ekA δ b D hA o χ' (pubsAOf δ b D hA o χ') ⟨j, hj⟩) (ezA δ b D hA o χ (pubsAOf δ b D hA o χ) ⟨j, hj⟩)
      (ezA δ b D hA o χ' (pubsAOf δ b D hA o χ') ⟨j, hj⟩)
      (by rw [ekA_chal, ekA_chal, chalsAZ_37, chalsAZ_37, hχ WeightsJ8.c2 (by decide)])
      (by rw [ekA_chal, ekA_chal, chalsAZ_38, chalsAZ_38, hχ WeightsJ8.c3 (by decide)])
      (ekA_trace δ b D hA o χ χ' _ _ hz _ 4 (by norm_num)).1 (ekA_trace δ b D hA o χ χ' _ _ hz _ 5 (by norm_num)).1
      (ezA_trace δ b D hA o χ χ' _ _ hz _ 2 (by norm_num)).1]
  · rfl

theorem famC_OK (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) : ∀ e ∈ famC δ b D hA o (K := K), e.OK := by
  intro e he
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp he
  refine ComplJ8Bad.quadPole_OK δ _ _ fun χ χ' hχ => ?_
  unfold cX
  split_ifs with hj
  · have hz := zA_c12 δ χ χ' hχ
    rw [ComplJ8Bad.γH_readsOff δ χ χ' hχ, keyVec5_congr 205 _ oldKey_below _ _
      (fun k hk => (ezA_trace δ b D hA o χ χ' _ _ hz _ k (by omega)).1)
      (fun k hk => (ezA_trace δ b D hA o χ χ' _ _ hz _ k (by omega)).2)]
  · rfl

theorem famMI_OK (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) : ∀ e ∈ famMI δ b D hA o (K := K), e.OK := by
  intro e he
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp he
  refine ComplJ8Bad.quadPole_OK δ _ _ fun χ χ' hχ => ?_
  unfold miX
  split_ifs with hj
  · have hz := zA_c12 δ χ χ' hχ
    rw [ComplJ8Bad.γH_readsOff δ χ χ' hχ, keyVec5_congr 205 _ incKey_below _ _
      (fun k hk => (ezA_trace δ b D hA o χ χ' _ _ hz _ k (by omega)).1)
      (fun k hk => (ezA_trace δ b D hA o χ χ' _ _ hz _ k (by omega)).2)]
  · rfl

/-- **Outside the atom families every atom denominator is non-zero.** -/
theorem atomPoles_good (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K)
    (gH : ∀ e ∈ famAH δ b D hA o (K := K), χ ∉ e.ev) (gMB : ∀ e ∈ famMB δ b D hA o (K := K), χ ∉ e.ev)
    (gC : ∀ e ∈ famC δ b D hA o (K := K), χ ∉ e.ev) (gMI : ∀ e ∈ famMI δ b D hA o (K := K), χ ∉ e.ev)
    (pubs : ℕ → K) :
    (∀ i, CellTraceHQ.dRow δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs (aCol δ b D χ) (mhvA D) i ≠ 0) ∧
    (∀ i, HonestA8.dMB δ b hA (powN o _) o (chalsAJ8Z δ χ) (pubsAOf δ b D hA o χ)
      (colAH δ b D hA o χ (pubsAOf δ b D hA o χ)) (newBA D) i ≠ 0) ∧
    (∀ i, HonestA8.dC δ b hA (powN o _) o (chalsAJ8Z δ χ) (pubsAOf δ b D hA o χ)
      (colAH δ b D hA o χ (pubsAOf δ b D hA o χ)) (newBA D) i ≠ 0) ∧
    (∀ i, HonestA8.dMI δ b hA (powN o _) o (chalsAJ8Z δ χ) (pubsAOf δ b D hA o χ)
      (colAH δ b D hA o χ (pubsAOf δ b D hA o χ)) (newBA D) i ≠ 0) := by
  have mem : ∀ (g : ℕ → BadSpec K) (i : Fin D.acs.length), g i ∈ (List.range D.acs.length).map g :=
    fun g i => List.mem_map.mpr ⟨i, List.mem_range.mpr i.isLt, rfl⟩
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [aRow_split]
    exact ComplJ8Bad.quadPole_ne δ _ _ χ _ (ComplJ8Bad.ρH_re δ χ) (gH _ (mem _ i))
  · rw [dMB_eq]
    have := ComplJ8Bad.quadPole_ne_mk δ _ (mbX δ b D hA o i) χ (χ WeightsJ8.c7) (gMB _ (mem _ i))
    simp only [mbX, dif_pos i.isLt, Fin.eta] at this
    exact this
  · rw [dC_eq]
    have := ComplJ8Bad.quadPole_ne δ _ (cX δ b D hA o i) χ _ (ComplJ8Bad.ρH_re δ χ) (gC _ (mem _ i))
    simp only [cX, dif_pos i.isLt, Fin.eta] at this
    exact this
  · rw [dMI_eq]
    have := ComplJ8Bad.quadPole_ne δ _ (miX δ b D hA o i) χ _ (ComplJ8Bad.ρH_re δ χ) (gMI _ (mem _ i))
    simp only [miX, dif_pos i.isLt, Fin.eta] at this
    exact this

end AtomFams

/-! ### The cell part's base columns are the generator's (`hcol`) -/

section AtomCol
open Nock.V1J8.Gen (hdN' tlN' atomV)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

theorem hdN_eq (n : Noun) : hdN n = hdN' n := by cases n <;> rfl
theorem tlN_eq (n : Noun) : tlN n = tlN' n := by cases n <;> rfl

theorem colAH_base (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) (k : ℕ)
    (hk : k < 129) :
    colAH δ b D hA o χ pubs k i = (ComplJ8Cell.cellRowBP δ (zA δ χ) (fun _ => none) D.acs (mvA D) (mxAF D)
      (fun _ => 0) (ptA D) D.acs[(i : ℕ)] i).base k := by
  simp only [colAH, CellTraceHQ.colHQ, extColF, if_pos hk, cellCol]
  rw [← ComplJ8Cell.cellRowsBP_getElem _ _ _ _ _ _ _ i.isLt]
  rfl

theorem colAH_fields (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) :
    let y := D.acs[(i : ℕ)]
    colAH δ b D hA o χ pubs Cell.idx i = ((i : ℕ) : ZMod p) ∧
    colAH δ b D hA o χ pubs Cell.idR i =
      (if (tlN' y).isCell then ((ComplJ8Data.ptrP p D.acs D.rows y : ℕ) : ZMod p) else 0) ∧
    colAH δ b D hA o χ pubs Cell.wL i = (((if (hdN' y).isCell then 1 else 0 : ℕ)) : ZMod p) ∧
    colAH δ b D hA o χ pubs Cell.wR i = (((if (tlN' y).isCell then 1 else 0 : ℕ)) : ZMod p) ∧
    colAH δ b D hA o χ pubs Cell.aL i = ((atomV (hdN' y) : ℕ) : ZMod p) ∧
    colAH δ b D hA o χ pubs Cell.aR i = ((atomV (tlN' y) : ℕ) : ZMod p) := by
  intro y
  have hy : D.acs[(i : ℕ)] = y := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [colAH_base δ b D hA o χ pubs i _ (by decide), hy]
  · rfl
  · show ComplJ8Cell.idRP (F := ZMod p) D.acs (fun _ => none) (ptA D) y = _
    unfold ComplJ8Cell.idRP ComplJ8Cell.idOf; rw [tlN_eq]; split_ifs <;> simp
  · show ComplJ8Cell.wOf (F := ZMod p) _ (hdN y) = _
    rw [hdN_eq]; unfold ComplJ8Cell.wOf ComplJ8Cell.isBig; cases (hdN' y).isCell <;> simp
  · show ComplJ8Cell.wOf (F := ZMod p) _ (tlN y) = _
    rw [tlN_eq]; unfold ComplJ8Cell.wOf ComplJ8Cell.isBig; cases (tlN' y).isCell <;> simp
  · show ComplJ8Cell.aOf (F := ZMod p) _ (hdN y) = _
    rw [hdN_eq]; unfold ComplJ8Cell.aOf ComplJ8Cell.isBig; cases hdN' y <;> simp [atomV, Noun.isCell]
  · show ComplJ8Cell.aOf (F := ZMod p) _ (tlN y) = _
    rw [tlN_eq]; unfold ComplJ8Cell.aOf ComplJ8Cell.isBig; cases tlN' y <;> simp [atomV, Noun.isCell]

end AtomCol

/-! ### The atom cell list at the run: cells, the rank bound from the row binder, tails -/

section AcsFacts
open Nock.V1J8.Gen (combOf spineOf hdN' tlN' atomV padN)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom (combOf_cons spineOf_cons2 spineOf_short mem_spineOf
  shape_acsP mem_acsP mem_spineL len_le_of_sub combOf_isCell tl_combOf genHyp_j8)

theorem internal_combOf : ∀ (l : List ℕ), 2 ≤ l.length → (combOf l).internal + 1 = l.length
  | [x, y], _ => rfl
  | x :: y :: z :: r, _ => by
    rw [combOf_cons x (y :: z :: r) (by simp)]
    have := internal_combOf (y :: z :: r) (by simp)
    simp only [Noun.internal, List.length_cons] at this ⊢
    omega

/-- A spine is duplicate-free (its rows have distinct internal counts) and has one row fewer than limbs. -/
theorem spineOf_facts : ∀ l : List ℕ, (spineOf l).Nodup ∧ l.length ≤ (spineOf l).length + 1
  | [] => by simp [spineOf_short [] (by simp)]
  | [x] => by simp [spineOf_short [x] (by simp)]
  | x :: y :: rest => by
    obtain ⟨ih1, ih2⟩ := spineOf_facts (y :: rest)
    rw [spineOf_cons2 (x :: y :: rest) (by simp), List.tail_cons]
    refine ⟨List.nodup_cons.mpr ⟨fun hm => ?_, ih1⟩, ?_⟩
    · obtain ⟨d, hd, he⟩ := (mem_spineOf _ _).mp hm
      have h1 := internal_combOf (x :: y :: rest) (by simp)
      have h2 := internal_combOf ((y :: rest).drop d) hd
      have h3 : ((y :: rest).drop d).length ≤ rest.length + 1 := by rw [List.length_drop]; simp
      have e : (combOf (x :: y :: rest)).internal = (combOf ((y :: rest).drop d)).internal := by
        rw [he]
      simp only [List.length_cons] at h1
      omega
    · simp only [List.length_cons] at ih2 ⊢
      omega

variable (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **The atom cell list of a generated run** (Goldilocks): every row is a cell, has rank `< 2^110` (from
`|acs| ≤ 2^31`: a spine's rows are distinct members of `acs`, so a comb has at most `|acs| + 1` limbs), and the
tail of a row is a row when it is a cell. -/
theorem acs_ok (hax : ComplJ8.ProgAxOK Nock.Atoms.p t) (hop5 : ComplJ8.ProgOp5OK Nock.Atoms.p t)
    (h31 : Rows31 (j8DataOf Nock.Atoms.p Rg Rt hgen)) :
    (∀ c ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).acs, c.isCell = true) ∧
    (∀ c ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).acs, rankOf c < 2 ^ 110) ∧
    (∀ c ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).acs, (tlN' c).isCell = true →
      tlN' c ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).acs) := by
  have hN : (j8DataOf Nock.Atoms.p Rg Rt hgen).rows.size ≤ 2 ^ 31 := by
    have h := h31 (bfsForest [(j8DataOf Nock.Atoms.p Rg Rt hgen).t]).length (by simp [sizesJ8])
    rw [ComplJ8BigBound.data_rows hgen]
    simpa [ComplJ8Data.rowsOfT, j8DataOf] using h
  have h31 : (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length ≤ 2 ^ 31 :=
    h31 _ (by simp [sizesJ8])
  have hg := genHyp_j8 Rg Rt hgen hax hop5 hN
  have hsp : ∀ a ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).bigs, ∀ x ∈ spineOf (Nock.Atoms.limbs a),
      x ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).acs := fun a ha x hx =>
    (mem_acsP _ _ x).mpr (Or.inl ((mem_spineL _ x).mpr ⟨a, ha, hx⟩))
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc htl => ?_⟩
  · obtain ⟨l, h2, -, hy, -⟩ := shape_acsP _ _ hg.big c hc
    rw [hy]; exact combOf_isCell l h2
  · obtain ⟨l, h2, -, hy, h3⟩ := shape_acsP _ _ hg.big c hc
    show c.internal < 2 ^ 110
    have e := internal_combOf l h2
    rw [hy]
    by_cases hl : 3 ≤ l.length
    · obtain ⟨-, a, ha, d, rfl⟩ := h3 hl
      have hs := len_le_of_sub (spineOf_facts (Nock.Atoms.limbs a)).1 (hsp a ha)
      have h4 := (spineOf_facts (Nock.Atoms.limbs a)).2
      have h5 : ((Nock.Atoms.limbs a).drop d).length ≤ (Nock.Atoms.limbs a).length := by
        rw [List.length_drop]; omega
      have : (2 : ℕ) ^ 31 + 2 < 2 ^ 110 := by norm_num
      omega
    · have : (2 : ℕ) < 2 ^ 110 := by norm_num
      omega
  · obtain ⟨l, h2, -, hy, h3⟩ := shape_acsP _ _ hg.big c hc
    rw [hy, tl_combOf l h2] at htl ⊢
    by_cases hl : 3 ≤ l.length
    · rw [if_pos hl]
      obtain ⟨-, a, ha, d, rfl⟩ := h3 hl
      refine hsp a ha _ ((mem_spineOf _ _).mpr ⟨d + 1, ?_, ?_⟩)
      · rw [List.length_drop] at hl ⊢; omega
      · rw [List.tail_drop]
    · rw [if_neg hl] at htl; simp [Noun.isCell] at htl

theorem idxD_eq : ∀ (cs : List Noun) (n : Noun), Nock.V1J8.Gen.idxD cs n = cs.idxOf n
  | [], n => by simp [Nock.V1J8.Gen.idxD]
  | c :: cs, n => by
    rw [List.idxOf_cons]
    by_cases h : c = n
    · simp [Nock.V1J8.Gen.idxD, h]
    · have hb : (c == n) = false := beq_eq_false_iff_ne.mpr h
      simp [Nock.V1J8.Gen.idxD, h, hb, idxD_eq cs n]

end AcsFacts

/-! ### `atomOK` at the run -/

section AtomRun
open Nock.V1J8.Gen (hdN' tlN' atomV)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

theorem pubsA_lo (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) :
    (∀ i < 2, pubsAOf δ b D hA o χ i = pub2 δ (avT δ D χ) i) ∧
    (∀ i, 2 ≤ i → i < 4 → pubsAOf δ b D hA o χ i = pub2 δ (axT δ D χ) i) ∧
    (∀ i, 4 ≤ i → i < 6 → pubsAOf δ b D hA o χ i = pub2 δ (ahT δ b D hA o χ) i) ∧
    (∀ i, 6 ≤ i → i < 8 → pubsAOf δ b D hA o χ i = pub2 δ (aTerm δ D AtomChipHQ.mb
      (HonestA8.dMB δ b hA (powN o _) o (chalsAJ8Z δ χ) (pubsA1 δ b D hA o χ)
        (colAH δ b D hA o χ (pubsA1 δ b D hA o χ)) (newBA D))) i) ∧
    (∀ i, 8 ≤ i → i < 10 → pubsAOf δ b D hA o χ i = pub2 δ (aTerm δ D AtomChipHQ.mi
      (HonestA8.dMI δ b hA (powN o _) o (chalsAJ8Z δ χ) (pubsA1 δ b D hA o χ)
        (colAH δ b D hA o χ (pubsA1 δ b D hA o χ)) (newBA D))) i) ∧
    (∀ i, 10 ≤ i → i < 12 → pubsAOf δ b D hA o χ i = pub2 δ (aTerm δ D AtomChipHQ.inc
      (HonestA8.dC δ b hA (powN o _) o (chalsAJ8Z δ χ) (pubsA1 δ b D hA o χ)
        (colAH δ b D hA o χ (pubsA1 δ b D hA o χ)) (newBA D))) i) := by
  refine ⟨fun i h1 => ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_,
    fun i h1 h2 => ?_⟩ <;> simp only [pubsAOf, pubsA1, pubsA0] <;> split_ifs <;> first | rfl | omega

/-- **The atom terminals at the trace's publics** (`hpub`, `hpMB`, `hpC`, `hpMI` of the chips): the publics are
defined at `pubsA0` / `pubsA1`; the denominators do not read the publics. -/
theorem atomTerms (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) :
    let P := pubsAOf δ b D hA o χ
    (∑ k ∈ Finset.range D.acs.length, vTermOf δ (cellFillInv δ (γV δ χ) (ρV δ χ) (aRows δ D χ k)) =
      Quad.mk _ (P 0) (P 1)) ∧
    (∑ k ∈ Finset.range D.acs.length, xTermOf δ (cellFillInv δ (γV δ χ) (ρV δ χ) (aRows δ D χ k)) =
      Quad.mk _ (P 2) (P 3)) ∧
    (Quad.mk _ (P CellHQ.pubHQ) (P (CellHQ.pubHQ + 1)) = ∑ j ∈ Finset.range D.acs.length,
      liftQ δ (CellTraceH.mN (mhvA D) j) *
        (CellTraceHQ.dN δ b hA (powN o _) o (chalsAJ8Z δ χ) P (aCol δ b D χ) (mhvA D) j)⁻¹) ∧
    (Quad.mk _ (P AtomChipHQ.pubMB) (P (AtomChipHQ.pubMB + 1)) = ∑ j ∈ Finset.range D.acs.length,
      liftQ δ (HonestA8.cNat j (newBA D AtomChipHQ.mb)) *
        (HonestA8.dNat δ (HonestA8.dMB δ b hA (powN o _) o (chalsAJ8Z δ χ) P (colAH δ b D hA o χ P) (newBA D)) j)⁻¹) ∧
    (Quad.mk _ (P AtomChipHQ.pubC) (P (AtomChipHQ.pubC + 1)) = ∑ j ∈ Finset.range D.acs.length,
      liftQ δ (HonestA8.cNat j (newBA D AtomChipHQ.inc)) *
        (HonestA8.dNat δ (HonestA8.dC δ b hA (powN o _) o (chalsAJ8Z δ χ) P (colAH δ b D hA o χ P) (newBA D)) j)⁻¹) ∧
    (Quad.mk _ (P AtomChipHQ.pubMI) (P (AtomChipHQ.pubMI + 1)) = ∑ j ∈ Finset.range D.acs.length,
      liftQ δ (HonestA8.cNat j (newBA D AtomChipHQ.mi)) *
        (HonestA8.dNat δ (HonestA8.dMI δ b hA (powN o _) o (chalsAJ8Z δ χ) P (colAH δ b D hA o χ P) (newBA D)) j)⁻¹) := by
  dsimp only
  obtain ⟨q01, q23, q45, q67, q89, q1011⟩ := pubsA_lo δ b D hA o χ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [q01 0 (by norm_num), q01 1 (by norm_num), pub2_mk2 δ _ 0 rfl]; rfl
  · rw [q23 2 (by norm_num) (by norm_num), q23 3 (by norm_num) (by norm_num), pub2_mk2 δ _ 2 rfl]; rfl
  · show Quad.mk _ (pubsAOf δ b D hA o χ 4) (pubsAOf δ b D hA o χ 5) = _
    rw [q45 4 (by norm_num) (by norm_num), q45 5 (by norm_num) (by norm_num), pub2_mk2 δ _ 4 rfl]
    unfold ahT
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dNHQ_pubs0 δ b hA (powN o _) o (chalsAJ8Z δ χ) (pubsA0 δ D χ) (aCol δ b D χ) (mhvA D) j,
      dNHQ_pubs0 δ b hA (powN o _) o (chalsAJ8Z δ χ) (pubsAOf δ b D hA o χ) (aCol δ b D χ) (mhvA D) j]
  · show Quad.mk _ (pubsAOf δ b D hA o χ 6) (pubsAOf δ b D hA o χ 7) = _
    rw [q67 6 (by norm_num) (by norm_num), q67 7 (by norm_num) (by norm_num), pub2_mk2 δ _ 6 rfl]
    unfold aTerm
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold HonestA8.dNat
    split_ifs
    · rw [dMB_pubs0 δ b D hA o χ (pubsA1 δ b D hA o χ), dMB_pubs0 δ b D hA o χ (pubsAOf δ b D hA o χ)]
    · rfl
  · show Quad.mk _ (pubsAOf δ b D hA o χ 10) (pubsAOf δ b D hA o χ 11) = _
    rw [q1011 10 (by norm_num) (by norm_num), q1011 11 (by norm_num) (by norm_num), pub2_mk2 δ _ 10 rfl]
    unfold aTerm
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold HonestA8.dNat
    split_ifs
    · rw [dC_pubs0 δ b D hA o χ (pubsA1 δ b D hA o χ), dC_pubs0 δ b D hA o χ (pubsAOf δ b D hA o χ)]
    · rfl
  · show Quad.mk _ (pubsAOf δ b D hA o χ 8) (pubsAOf δ b D hA o χ 9) = _
    rw [q89 8 (by norm_num) (by norm_num), q89 9 (by norm_num) (by norm_num), pub2_mk2 δ _ 8 rfl]
    unfold aTerm
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold HonestA8.dNat
    split_ifs
    · rw [dMI_pubs0 δ b D hA o χ (pubsA1 δ b D hA o χ), dMI_pubs0 δ b D hA o χ (pubsAOf δ b D hA o χ)]
    · rfl

variable (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **The rows bound from `h31`**: the `GenHyp.rows31` input of `genHyp_j8` / `genHyp_mb`,
by the recipe of `noIncCorner_of_j8` (`data_rows hgen` + `rowsOfT`). -/
theorem rows_le_of_rows31 (h31 : Rows31 (j8DataOf p Rg Rt hgen)) :
    (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31 := by
  have h := h31 (bfsForest [(j8DataOf p Rg Rt hgen).t]).length (by simp [sizesJ8])
  rw [ComplJ8BigBound.data_rows hgen]
  simpa [ComplJ8Data.rowsOfT, j8DataOf] using h

/-- **`atomOK` at the run** (the `OpenJ8.atomOK` field at `BOf … (avOf …) fams`, Goldilocks), given the six atom
pole families (`famAZ famAV famAH famMB famC famMI`) are in `fams`.  Rank bound from `h31`; `hcor`: no inc corner
(GLA fix (B); `atomOK_run` below discharges it under `complJ8`'s binders). -/
theorem atomOK_run_gen (hpG : p = Nock.Atoms.p) (hF : DvdOK (j8DataOf p Rg Rt hgen))
    (hC : 0 < (j8DataOf p Rg Rt hgen).cells.length) (hA : 0 < (j8DataOf p Rg Rt hgen).acs.length)
    (fams : List (List (BadSpec K))) (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hlast : Nock.V1J8.Gen.lastIdxOf (j8DataOf p Rg Rt hgen).acs (ComplJ8Data.combPP p) =
      Nock.V1J8.Gen.idxOf (j8DataOf p Rg Rt hgen).acs (ComplJ8Data.combPP p))
    (mZ : famAZ (K := K) ∈ fams) (mV : famAV δ (j8DataOf p Rg Rt hgen) ∈ fams)
    (mH : famAH δ b (j8DataOf p Rg Rt hgen) hA (orbJ8 _ hF) ∈ fams)
    (mMB : famMB δ b (j8DataOf p Rg Rt hgen) hA (orbJ8 _ hF) ∈ fams)
    (mC : famC δ b (j8DataOf p Rg Rt hgen) hA (orbJ8 _ hF) ∈ fams)
    (mMI : famMI δ b (j8DataOf p Rg Rt hgen) hA (orbJ8 _ hF) ∈ fams)
    (χ : Coins frameJ8 K)
    (hχ : (BOf δ b Rt hgen hF hC hA (avOf δ b (j8DataOf p Rg Rt hgen) hF hA) fams).Good χ) :
    let B := BOf δ b Rt hgen hF hC hA (avOf δ b (j8DataOf p Rg Rt hgen) hF hA) fams
    (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (AcceptsJ8.qA δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (AcceptsJ8.qA δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (AcceptsJ8L.qAL δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (AcceptsJ8L.qAL δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) := by
  intro B
  subst hpG
  have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(j8DataOf Nock.Atoms.p Rg Rt hgen).t]).length)] fams),
      χ ∉ e.1 := hχ
  have hin : ∀ L ∈ fams, ∀ e ∈ L, χ ∉ e.ev := fun L hL e he =>
    ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨L, hL, he⟩))
  have hz := famAZ_good δ χ (hin _ mZ)
  have hv := famAV_good δ (j8DataOf Nock.Atoms.p Rg Rt hgen) χ (hin _ mV)
  obtain ⟨hpH, hpMB, hpC, hpMI⟩ := atomPoles_good δ b (j8DataOf Nock.Atoms.p Rg Rt hgen) hA (orbJ8 _ hF) χ
    (hin _ mH) (hin _ mMB) (hin _ mC) (hin _ mMI) (pubsAOf δ b (j8DataOf Nock.Atoms.p Rg Rt hgen) hA (orbJ8 _ hF) χ)
  have hmA : (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length ∈ sizesJ8 (j8DataOf Nock.Atoms.p Rg Rt hgen) := by
    simp [sizesJ8]
  obtain ⟨hcell, hrank, htl⟩ := acs_ok Rg Rt hgen hax hop5 h31
  obtain ⟨hinj, hadj⟩ := powN_ok (orbJ8 _ hF) (le_two_pow_ht _ hmA)
  obtain ⟨tV, tX, tH, tMB, tC, tMI⟩ := atomTerms δ b (j8DataOf Nock.Atoms.p Rg Rt hgen) hA (orbJ8 _ hF) χ
  have hsat0 := ComplJ8Cell.cellChipHQ_honest_listP δ b hA (powN (orbJ8 _ hF) _) (orbJ8 _ hF) (chalsAJ8Z δ χ)
    (pubsAOf δ b (j8DataOf Nock.Atoms.p Rg Rt hgen) hA (orbJ8 _ hF) χ) (γV δ χ) (ρV δ χ) (zA δ χ) (fun _ => none)
    (j8DataOf Nock.Atoms.p Rg Rt hgen).acs (mvA _) (mxAF _) (fun _ => 0) (ptA _) (mhvA _) hcell hrank rfl hinj hadj
    (ChalsAZJ8.chalsAJ8Z_ok δ χ) rfl hz (fun j hj => (hv j hj).1) (fun j hj _ => (hv j hj).2.1)
    (fun j hj _ => (hv j hj).2.2.1) (fun j hj => (hv j hj).2.2.2.1) (fun j hj => (hv j hj).2.2.2.2)
    tV tX hpH tH
  have hcol : ∀ i : Fin (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      let y := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs[(i : ℕ)]
      colAH δ b _ hA (orbJ8 _ hF) χ (pubsAOf δ b _ hA (orbJ8 _ hF) χ) Cell.idx i = ((i : ℕ) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA (orbJ8 _ hF) χ (pubsAOf δ b _ hA (orbJ8 _ hF) χ) Cell.idR i =
        (((if (tlN' y).isCell then ComplJ8Data.ptrP Nock.Atoms.p (j8DataOf Nock.Atoms.p Rg Rt hgen).acs
            (j8DataOf Nock.Atoms.p Rg Rt hgen).rows y else 0 : ℕ))
          : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA (orbJ8 _ hF) χ (pubsAOf δ b _ hA (orbJ8 _ hF) χ) Cell.wL i =
        (((if (hdN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA (orbJ8 _ hF) χ (pubsAOf δ b _ hA (orbJ8 _ hF) χ) Cell.wR i =
        (((if (tlN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA (orbJ8 _ hF) χ (pubsAOf δ b _ hA (orbJ8 _ hF) χ) Cell.aL i =
        ((atomV (hdN' y) : ℕ) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA (orbJ8 _ hF) χ (pubsAOf δ b _ hA (orbJ8 _ hF) χ) Cell.aR i =
        ((atomV (tlN' y) : ℕ) : ZMod Nock.Atoms.p) := by
    intro i y
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := colAH_fields δ b _ hA (orbJ8 _ hF) χ
      (pubsAOf δ b _ hA (orbJ8 _ hF) χ) i
    refine ⟨c1, ?_, c3, c4, c5, c6⟩
    rw [c2]
    by_cases hc : (tlN' y).isCell = true
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]; simp
  have res := ComplJ8AW.atomOK_j8_gen δ b Rg Rt hgen hA (powN (orbJ8 _ hF) _) (orbJ8 _ hF) (chalsAJ8Z δ χ)
    (pubsAOf δ b _ hA (orbJ8 _ hF) χ) (colAH δ b _ hA (orbJ8 _ hF) χ (pubsAOf δ b _ hA (orbJ8 _ hF) χ))
    hax hop5 (rows_le_of_rows31 Rt hgen h31) hinj hadj hcol hsat0 hpMB hpC hpMI tMB tC tMI
  exact res

/-- **`lastIdxOf = idxOf` at `comb p` under `complJ8`'s binders** (J-8: `bigBound_single`; the premise of
`ComplJ8Data.ptrP_eq_idxOf`). -/
theorem last_eq_of_j8 (hpG : p = Nock.Atoms.p) (hop5 : ComplJ8.ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen)) :
    Nock.V1J8.Gen.lastIdxOf (j8DataOf p Rg Rt hgen).acs (ComplJ8Data.combPP p) =
      Nock.V1J8.Gen.idxOf (j8DataOf p Rg Rt hgen).acs (ComplJ8Data.combPP p) :=
  (ComplJ8BigBound.bigBound_single hgen hpG (hclA 0) (hclA 1) hRt hop5
    (rows_le_of_rows31 Rt hgen h31)).2.2.2.2.1


theorem noIncCorner_of_j8 (hpG : p = Nock.Atoms.p) (hop5 : ComplJ8.ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen)) :
    ComplJ8Atom.NoIncCornerP p (j8DataOf p Rg Rt hgen).acs (ComplJ8Data.incOpsP p (j8DataOf p Rg Rt hgen).rows) := by
  have hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31 := by
    have h := h31 (bfsForest [(j8DataOf p Rg Rt hgen).t]).length (by simp [sizesJ8])
    rw [ComplJ8BigBound.data_rows hgen]
    simpa [ComplJ8Data.rowsOfT, j8DataOf] using h
  exact ComplJ8Atom.noIncCorner_of_last
    (ComplJ8BigBound.bigBound_single hgen hpG (hclA 0) (hclA 1) hRt hop5 hN).2.2.2.2.1

/-- **`atomOK` at the run** (the `OpenJ8.atomOK` field at `BOf … (avOf …) fams`, Goldilocks), given the six atom
pole families (`famAZ famAV famAH famMB famC famMI`) are in `fams`.  Rank bound from `h31`.  NARROWED by GLA fix (B): `+ hclA hRt` (was `hpG hax hop5 h31`); with the
fixed generator the conclusion is false at `hax hop5 h31` alone (the inc corner run, `Batch4851.noIncCorner_neg`). -/
theorem atomOK_run (hpG : p = Nock.Atoms.p) (hF : DvdOK (j8DataOf p Rg Rt hgen))
    (hC : 0 < (j8DataOf p Rg Rt hgen).cells.length) (hA : 0 < (j8DataOf p Rg Rt hgen).acs.length)
    (fams : List (List (BadSpec K))) (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (mZ : famAZ (K := K) ∈ fams) (mV : famAV δ (j8DataOf p Rg Rt hgen) ∈ fams)
    (mH : famAH δ b (j8DataOf p Rg Rt hgen) hA (orbJ8 _ hF) ∈ fams)
    (mMB : famMB δ b (j8DataOf p Rg Rt hgen) hA (orbJ8 _ hF) ∈ fams)
    (mC : famC δ b (j8DataOf p Rg Rt hgen) hA (orbJ8 _ hF) ∈ fams)
    (mMI : famMI δ b (j8DataOf p Rg Rt hgen) hA (orbJ8 _ hF) ∈ fams)
    (χ : Coins frameJ8 K)
    (hχ : (BOf δ b Rt hgen hF hC hA (avOf δ b (j8DataOf p Rg Rt hgen) hF hA) fams).Good χ) :
    let B := BOf δ b Rt hgen hF hC hA (avOf δ b (j8DataOf p Rg Rt hgen) hF hA) fams
    (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (AcceptsJ8.qA δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (AcceptsJ8.qA δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (AcceptsJ8L.qAL δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (AcceptsJ8L.qAL δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) :=
  atomOK_run_gen δ b Rt hgen hpG hF hC hA fams hax hop5 h31 (last_eq_of_j8 Rt hgen hpG hop5 hclA hRt h31)
    mZ mV mH mMB mC mMI χ hχ

end AtomRun

/-! ## 3. The families together (for `famsOf`) -/

section Fams
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (nPins)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- **The eight atom-table and atom-walk pole families** (to be appended to `famsOf`). -/
def famsA (D : J8Data p Rg fuel s f r) (hF : DvdOK D) (hA : 0 < D.acs.length) : List (List (BadSpec K)) :=
  [famAZ, famAV δ D, famAH δ b D hA (orbJ8 D hF), famMB δ b D hA (orbJ8 D hF), famC δ b D hA (orbJ8 D hF),
    famMI δ b D hA (orbJ8 D hF), famAWV δ D, famAWH δ D]

/-- **The families: side conditions, pins only, pin count `≤ 1 + 9·|acs| + 6·nV`.** -/
theorem famsA_facts (D : J8Data p Rg fuel s f r) (hF : DvdOK D) (hA : 0 < D.acs.length) :
    (∀ L ∈ famsA δ b D hF hA (K := K), ∀ e ∈ L, e.OK) ∧
    (∀ L ∈ famsA δ b D hF hA (K := K), ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N) ∧
    ((famsA δ b D hF hA (K := K)).map nPins).sum ≤ 1 + 9 * D.acs.length + 6 * nVOf D := by
  have pZ : AllPin (famAZ (K := K)) := fun e he => by
    simp only [famAZ, List.mem_singleton] at he; subst he; exact ⟨_, _, rfl⟩
  have pV : AllPin (famAV δ D (K := K)) :=
    allPin_flatMap _ _ fun j _ => allPin_map _ _ fun x => ⟨_, _, rfl⟩
  have pH : AllPin (famAH δ b D hA (orbJ8 D hF) (K := K)) := allPin_map _ _ fun x => ⟨_, _, rfl⟩
  have pMB : AllPin (famMB δ b D hA (orbJ8 D hF) (K := K)) := allPin_map _ _ fun x => ⟨_, _, rfl⟩
  have pC : AllPin (famC δ b D hA (orbJ8 D hF) (K := K)) := allPin_map _ _ fun x => ⟨_, _, rfl⟩
  have pMI : AllPin (famMI δ b D hA (orbJ8 D hF) (K := K)) := allPin_map _ _ fun x => ⟨_, _, rfl⟩
  have pWV : AllPin (famAWV δ D (K := K)) :=
    allPin_flatMap _ _ fun j _ => allPin_map _ _ fun x => ⟨_, _, rfl⟩
  have pWH : AllPin (famAWH δ D (K := K)) :=
    allPin_flatMap _ _ fun j _ => allPin_map _ _ fun x => ⟨_, _, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro L hL
    simp only [famsA, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact famAZ_OK
    · exact famAV_OK δ D
    · exact famAH_OK δ b D hA _
    · exact famMB_OK δ b D hA _
    · exact famC_OK δ b D hA _
    · exact famMI_OK δ b D hA _
    · exact famAWV_OK δ D
    · exact famAWH_OK δ D
  · intro L hL e he i N hN
    simp only [famsA, List.mem_cons, List.not_mem_nil, or_false] at hL
    have hp : AllPin L := by
      rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [pZ, pV, pH, pMB, pC, pMI, pWV, pWH]
    obtain ⟨j, g, rfl⟩ := hp e he
    cases hN
  · have l1 : (famAV δ D (K := K)).length ≤ D.acs.length * 5 := by
      unfold famAV
      exact (ComplJ8Of.length_flatMap_le _ _ 5 fun j _ => le_of_eq (by rw [List.length_map]; rfl)).trans (by rw [List.length_range])
    have l2 : (famAWV δ D (K := K)).length ≤ nVOf D * 3 := by
      unfold famAWV
      exact (ComplJ8Of.length_flatMap_le _ _ 3 fun j _ => le_of_eq (by rw [List.length_map]; rfl)).trans (by rw [List.length_range])
    have l3 : (famAWH δ D (K := K)).length ≤ nVOf D * 3 := by
      unfold famAWH
      refine (ComplJ8Of.length_flatMap_le _ _ 3 fun j _ => ?_).trans (by rw [List.length_range])
      rw [List.length_map]; unfold awHx; split_ifs
      · exact le_of_eq rfl
      · exact Nat.zero_le _
    simp only [famsA, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have := nPins_le_length (famAZ (K := K))
    have := nPins_le_length (famAV δ D (K := K))
    have := nPins_le_length (famAH δ b D hA (orbJ8 D hF) (K := K))
    have := nPins_le_length (famMB δ b D hA (orbJ8 D hF) (K := K))
    have := nPins_le_length (famC δ b D hA (orbJ8 D hF) (K := K))
    have := nPins_le_length (famMI δ b D hA (orbJ8 D hF) (K := K))
    have := nPins_le_length (famAWV δ D (K := K))
    have := nPins_le_length (famAWH δ D (K := K))
    have e1 : (famAZ (K := K)).length = 1 := rfl
    have e2 : (famAH δ b D hA (orbJ8 D hF) (K := K)).length = D.acs.length := by rw [famAH, List.length_map, List.length_range]
    have e3 : (famMB δ b D hA (orbJ8 D hF) (K := K)).length = D.acs.length := by rw [famMB, List.length_map, List.length_range]
    have e4 : (famC δ b D hA (orbJ8 D hF) (K := K)).length = D.acs.length := by rw [famC, List.length_map, List.length_range]
    have e5 : (famMI δ b D hA (orbJ8 D hF) (K := K)).length = D.acs.length := by rw [famMI, List.length_map, List.length_range]
    omega

end Fams

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom

/-!

`ComplJ8Atom.valid_j8` and `ComplJ8AW.atomOK_j8` are NARROWED: `+ hclA hRt h31` (was `hax hop5`).  With the fixed
generator (the depth-0 inc row of `p` keys the last copy of `comb p`) their conclusions are false at `hax hop5` alone:
the inc corner run `s = [p·B u]`, `u = [B−1, 1, B−1]`, `f = [[4 [4 [1 p−1]]] [4 [0 3]]]` fails the atom chip's link1
(`Batch4851.noIncCorner_neg`).  They are re-derived from `valid_j8_gen` / `atomOK_j8_gen` by `noIncCorner_of_j8`
.  They live here because `bigBound_single` and `Rows31` sit above `ComplJ8Atom` /
`ComplJ8AW`.  Both take the instance `[Fact (ringChar (ZMod p)).Prime]` at Goldilocks, which `Rows31` reads. -/

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom
open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (j8DataOf)
variable (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **The generator's atom table is valid** for every generated run at Goldilocks, under `complJ8`'s binders
`hax hop5 hclA hRt h31` (NARROWED by GLA fix (B): was `hax hop5`). -/
theorem valid_j8 [Fact (ringChar (ZMod Nock.Atoms.p)).Prime] (hax : ComplJ8.ProgAxOK Nock.Atoms.p t) (hop5 : ComplJ8.ProgOp5OK Nock.Atoms.p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < Nock.Atoms.p)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate Nock.Atoms.p,
      Nock.Jet.Autogen.compile Nock.Atoms.p (Rt id)⟩ ∧ Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧
      (Rt id).WellTyped Nock.Atoms.p)
    (h31 : ComplJ8Of.Rows31 (j8DataOf Nock.Atoms.p Rg Rt hgen))
    :
    (tabOf (j8DataOf Nock.Atoms.p Rg Rt hgen).acs (j8DataOf Nock.Atoms.p Rg Rt hgen).info
      (j8DataOf Nock.Atoms.p Rg Rt hgen).mb (j8DataOf Nock.Atoms.p Rg Rt hgen).rows).Valid :=
  valid_j8_gen Rg Rt hgen hax hop5 (ComplJ8OfAtom.rows_le_of_rows31 Rt hgen h31)

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8AW
open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK
open Module
section J8Old
open Nock.V1J8.Gen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (atomChipHQ pubMB pubC pubMI mb inc mi)
open Nock.Edit Nock.Edit.GenX

variable {K : Type} [Field K] [Algebra (ZMod Nock.Atoms.p) K] [FiniteDimensional (ZMod Nock.Atoms.p) K]
  [Fintype K] (δ : ZMod Nock.Atoms.p) [Fact (¬ IsSquare (algebraMap (ZMod Nock.Atoms.p) K δ))]
  (b : Basis (Fin 3) (ZMod Nock.Atoms.p) K)
  (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  {hA : ℕ} (hn : 0 < (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length)
  (nodes : Fin (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length → ZMod Nock.Atoms.p)
  (orbit : StrictOrbitDomain (ZMod Nock.Atoms.p) 3 hA) (chals pubs : ℕ → K)
  (col : ℕ → Fin (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length → ZMod Nock.Atoms.p)

/-- **The generator's atom table at a good coin** (J-8 instance, Goldilocks), under `complJ8`'s binders
`hax hop5 hclA hRt h31` (NARROWED by GLA fix (B): was `hax hop5`); `atomOK_j8_gen` with `noIncCorner_of_j8`. -/
theorem atomOK_j8 [Fact (ringChar (ZMod Nock.Atoms.p)).Prime] (hax : ComplJ8.ProgAxOK Nock.Atoms.p t) (hop5 : ComplJ8.ProgOp5OK Nock.Atoms.p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < Nock.Atoms.p)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate Nock.Atoms.p,
      Nock.Jet.Autogen.compile Nock.Atoms.p (Rt id)⟩ ∧ Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧
      (Rt id).WellTyped Nock.Atoms.p)
    (h31 : ComplJ8Of.Rows31 (j8DataOf Nock.Atoms.p Rg Rt hgen))
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin _) (hi : (i : ℕ) + 1 < (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length),
      nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hcol : ∀ i : Fin (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      let y := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs[(i : ℕ)]
      col Cell.idx i = ((i : ℕ) : ZMod Nock.Atoms.p) ∧
      col Cell.idR i = (((if (tlN' y).isCell then idxOf (j8DataOf Nock.Atoms.p Rg Rt hgen).acs (tlN' y) else 0 : ℕ))
        : ZMod Nock.Atoms.p) ∧
      col Cell.wL i = (((if (hdN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      col Cell.wR i = (((if (tlN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      col Cell.aL i = ((atomV (hdN' y) : ℕ) : ZMod Nock.Atoms.p) ∧
      col Cell.aR i = ((atomV (tlN' y) : ℕ) : ZMod Nock.Atoms.p))
    (hsat0 : (cellChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies (honestQ hn nodes col _))
    (hz1 : ∀ i, HonestA8.dMB δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen)) i ≠ 0)
    (hz2 : ∀ i, HonestA8.dC δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen)) i ≠ 0)
    (hz3 : ∀ i, HonestA8.dMI δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen)) i ≠ 0)
    (hpMB : Quad.mk _ (pubs pubMB) (pubs (pubMB + 1)) = ∑ j ∈ Finset.range (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      liftQ δ (HonestA8.cNat j (newOf (n := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length) (rowsJ8 Rg Rt hgen) mb)) *
        (HonestA8.dNat δ (HonestA8.dMB δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen))) j)⁻¹)
    (hpC : Quad.mk _ (pubs pubC) (pubs (pubC + 1)) = ∑ j ∈ Finset.range (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      liftQ δ (HonestA8.cNat j (newOf (n := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length) (rowsJ8 Rg Rt hgen) inc)) *
        (HonestA8.dNat δ (HonestA8.dC δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen))) j)⁻¹)
    (hpMI : Quad.mk _ (pubs pubMI) (pubs (pubMI + 1)) = ∑ j ∈ Finset.range (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      liftQ δ (HonestA8.cNat j (newOf (n := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length) (rowsJ8 Rg Rt hgen) mi)) *
        (HonestA8.dNat δ (HonestA8.dMI δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen))) j)⁻¹) :
    (atomChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies
        (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen))) ∧
      (atomChipHQ δ b hn nodes orbit chals pubs).BindsPreprocessing
        (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen))) ∧
      (AtomChipHQL.atomChipHQL δ b hn nodes orbit chals pubs).rap.Satisfies
        (AtomChipHQL.ofHQ δ b hn nodes orbit chals pubs
          (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen)))) ∧
      (AtomChipHQL.atomChipHQL δ b hn nodes orbit chals pubs).BindsPreprocessing
        (AtomChipHQL.ofHQ δ b hn nodes orbit chals pubs
          (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (rowsJ8 Rg Rt hgen)))) :=
  atomOK_j8_gen δ b Rg Rt hgen hn nodes orbit chals pubs col hax hop5
    (ComplJ8OfAtom.rows_le_of_rows31 Rt hgen h31) hinj hadj
    (fun i => by
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcol i
      refine ⟨c1, ?_, c3, c4, c5, c6⟩
      rw [c2]
      by_cases hc : (tlN' (j8DataOf Nock.Atoms.p Rg Rt hgen).acs[(i : ℕ)]).isCell = true
      · rw [if_pos hc, if_pos hc, ComplJ8Data.ptrP_eq_idxOf _ _ _
          (ComplJ8OfAtom.last_eq_of_j8 Rt hgen rfl hop5 hclA hRt h31)]
      · rw [if_neg hc, if_neg hc]) hsat0 hz1 hz2 hz3 hpMB hpC hpMI

end J8Old

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8AW
