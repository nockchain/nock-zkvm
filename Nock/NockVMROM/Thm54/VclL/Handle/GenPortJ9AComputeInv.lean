/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AComputeInv.lean

  `env0 = envX9` (given `chalV = Example.chalE χe`, `pubVal = pub`), then the limb
  equalities `compTable9 … [j][d] = trX9 … j (invPermX9 d)` for `invPermX9 d ∈ [69, 93)`. -/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ACompute

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ACompute

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow (invPermX9 colX9)
open Nock.NockVMROM.Thm54.VclL.HonestWalkX9 (rowAt9 fl1 llW)
open Nock.V1J9A.GenCompX9
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP

/-- The honest stage-1 columns are the executable base columns. -/
theorem baseT9_eq_baseFn9 (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (j : ℕ) :
    Nock.NockVMROM.Thm54.VclL.HonestTraceX9.baseT9 (F := ZMod P) H pd idOf W j = baseFn9 H pd idOf W j := by
  funext c
  unfold Nock.NockVMROM.Thm54.VclL.HonestTraceX9.baseT9 baseFn9
  haveI : CharP (ZMod P) P := ZMod.charP P
  rw [Nock.V1J9A.FillX9.colX9E_eq]

/-- **`env0 = envX9`**: the honest stage-1 environment is the executable one (coins `chalV = chalE χe`). -/
theorem env0_eq_envX9 (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (pub : ℕ → ZMod P) (χe : CoinsE) (j : ℕ) :
    Nock.NockVMROM.Thm54.VclL.HonestTraceX9.env0 H pd idOf W (Example.chalE χe) pub j =
      envX9 H pd idOf W pub χe j := by
  unfold Nock.NockVMROM.Thm54.VclL.HonestTraceX9.env0 envX9
  rw [baseT9_eq_baseFn9, baseT9_eq_baseFn9]

/-- Reading the `k`-th limb of `K3.toK w` through `cNA` is `limbZ`. -/
theorem cNA_toK (w : K3) (k : ℕ) (hk : k < 3) :
    Nock.NockVMROM.Thm54.VclL.HonestTraceX.cNA powerBasis3 (K3.toK w) k = limbZ w k := by
  unfold Nock.NockVMROM.Thm54.VclL.HonestTraceX.cNA
  rw [dif_pos hk]
  exact coord_K w k hk

/-- The honest `𝕂′` slot inverse, real and imaginary parts, are the `K3.toK` of the executable `K6` inverse. -/
theorem invV9_re_im (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (pub : ℕ → ZMod P) (χe : CoinsE) (j s : ℕ) :
    (Quad.re _ (Nock.NockVMROM.Thm54.VclL.HonestTraceX9.invV9 powerBasis3 deltaF H pd idOf W (Example.chalE χe)
        pub j (Nock.NockVMROM.Thm54.VclL.HonestTraceX9.slotAt9 s)) =
      K3.toK (invE9 (envX9 H pd idOf W pub χe j) s).re) ∧
    (Quad.im _ (Nock.NockVMROM.Thm54.VclL.HonestTraceX9.invV9 powerBasis3 deltaF H pd idOf W (Example.chalE χe)
        pub j (Nock.NockVMROM.Thm54.VclL.HonestTraceX9.slotAt9 s)) =
      K3.toK (invE9 (envX9 H pd idOf W pub χe j) s).im) := by
  have h := toQ_invE9 (envX9 H pd idOf W pub χe j) s
  have e : Nock.NockVMROM.Thm54.VclL.HonestTraceX9.invV9 powerBasis3 deltaF H pd idOf W (Example.chalE χe)
        pub j (Nock.NockVMROM.Thm54.VclL.HonestTraceX9.slotAt9 s) =
      K6.toQ (invE9 (envX9 H pd idOf W pub χe j) s) := by
    rw [h]
    unfold Nock.NockVMROM.Thm54.VclL.HonestTraceX9.invV9
    rw [env0_eq_envX9]
  rw [e]
  unfold K6.toQ
  exact ⟨Quad.re_mk _ _ _, Quad.im_mk _ _ _⟩

/-- The table's inverse array entry is the executable inverse (`j < |W|`, `s < 4`). -/
theorem invs_getD (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (pub : ℕ → ZMod P) (χe : CoinsE) {j : ℕ} (hj : j < W.length) {s : ℕ} (hs : s < 4) :
    (((((List.range W.length).map fun j => envX9 H pd idOf W pub χe j).map invsOf9).getD j #[]).getD s 0) =
      invE9 (envX9 H pd idOf W pub χe j) s := by
  simp only [List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, Function.comp]
  unfold invsOf9
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hs]

/-- **Slot-inverse columns** (twin `69..92`): the executable table is `trX9` (at `F = ZMod P`, `K = KC`,
`b = powerBasis3`, `δ = deltaF`, `chalV = Example.chalE χe`, `pubVal = pub`). -/
theorem compTable9_eq_trX9_inv
    [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
    (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (pub : ℕ → ZMod P) (χe : CoinsE) (ln cnt acc : ℕ → KC)
    {j : ℕ} (hj : j < W.length) {d : ℕ} (hd : d < 137)
    (hr : 69 ≤ invPermX9 d ∧ invPermX9 d < 93) :
    ((compTable9 H pd idOf W pub χe).getD j #[]).getD d 0 =
      Nock.NockVMROM.Thm54.VclL.HonestTraceX9.trX9 powerBasis3 deltaF H pd idOf W (Example.chalE χe) pub
        ln cnt acc j (invPermX9 d) := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨s, o, hs, ho, hc⟩ : ∃ s o, s < 4 ∧ o < 6 ∧ invPermX9 d = 69 + 6 * s + o :=
    ⟨(invPermX9 d - 69) / 6, (invPermX9 d - 69) % 6, by omega, by omega, by omega⟩
  rw [compTable9_getD H pd idOf W pub χe hj hd, hc,
    Nock.NockVMROM.Thm54.VclL.HonestTraceX9.trX9_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs ho]
  have h1 : (69 + 6 * s + o - 69) / 6 = s := by omega
  have h2 : (69 + 6 * s + o - 69) % 6 = o := by omega
  have hiv := invs_getD H pd idOf W pub χe hj hs
  have hre := (invV9_re_im H pd idOf W pub χe j s)
  simp only [compColD9]
  rw [if_neg (by omega : ¬ (69 + 6 * s + o < 69 ∨ 123 ≤ 69 + 6 * s + o)),
    if_pos (by omega : 69 + 6 * s + o < 93)]
  simp only [h1, h2, hiv]
  split_ifs with ho3
  · rw [(hre).1, cNA_toK _ _ ho3]
  · rw [(hre).2, cNA_toK _ _ (by omega)]

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ACompute

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ACompute.env0_eq_envX9
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ACompute.invV9_re_im
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ACompute.compTable9_eq_trX9_inv
