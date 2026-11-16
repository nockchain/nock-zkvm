/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ACompute.lean

  Proved here: the table access lemma (`compTable9_getD`), and the BASE columns
  (round-0 columns `r0 (invPermX9 c)`) `compGenX9_base_eq`. -/
import Nock.V1J9A.GenCompX9

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

/-- **Table access**: row `j < |W|`, RAP column `d < 137` of `compTable9` is `compColD9` at `invPermX9 d`. -/
theorem compTable9_getD (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (pub : ℕ → ZMod P) (χe : CoinsE) {j : ℕ} (hj : j < W.length) {d : ℕ} (hd : d < 137) :
    ((compTable9 H pd idOf W pub χe).getD j #[]).getD d 0 =
      (let es := (List.range W.length).map fun j => envX9 H pd idOf W pub χe j
       let ivs := es.map invsOf9
       let accs := (prefixSums 18 ((es.zip ivs).map fun (e, iv) => termRow9 e iv)).1
       let wv := walkVals9 H pd idOf W (χe ⟨13, by decide⟩) (χe ⟨14, by decide⟩)
       compColD9 (baseFn9 H pd idOf W j) (ivs.getD j #[]) (accs.getD j #[]) (wv.getD j (0, 0, 0, 0))
         (invPermX9 d)) := by
  unfold compTable9
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, Array.getElem?_ofFn]
  simp [hd]

/-- **Base columns**: for `j < |W|` and a RAP column `d < 137` whose twin column is a round-0 column, the table entry
is the honest builder `colX9` of BFS row `j + 1` (this is `trX9`'s base value). -/
theorem compTable9_base (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (pub : ℕ → ZMod P) (χe : CoinsE) {j : ℕ} (hj : j < W.length) {d : ℕ} (hd : d < 137)
    (hr : invPermX9 d < 69 ∨ 123 ≤ invPermX9 d) :
    ((compTable9 H pd idOf W pub χe).getD j #[]).getD d 0 =
      colX9 H pd idOf (rowAt9 W (j + 1)) (fl1 (j + 1)) (llW W (j + 1)) (invPermX9 d) := by
  rw [compTable9_getD H pd idOf W pub χe hj hd]
  simp only [compColD9, if_pos (show invPermX9 d < 69 ∨ 123 ≤ invPermX9 d from hr)]
  unfold baseFn9
  haveI : CharP (ZMod P) P := ZMod.charP P
  rw [Nock.V1J9A.FillX9.colX9E_eq]

/-- **Base columns = `trX9`** (any basis, coins, publics and walk functions: the round-0 columns do not read them). -/
theorem compTable9_eq_trX9_base {K : Type} [Field K] [Algebra (ZMod P) K] [FiniteDimensional (ZMod P) K]
    [Fintype K] (b : Module.Basis (Fin 3) (ZMod P) K) (δ : ZMod P)
    [Fact (¬ IsSquare (algebraMap (ZMod P) K δ))]
    (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (pub : ℕ → ZMod P) (χe : CoinsE) (chalV pubVal : ℕ → ZMod P) (ln cnt acc : ℕ → K)
    {j : ℕ} (hj : j < W.length) {d : ℕ} (hd : d < 137)
    (hr : invPermX9 d < 69 ∨ 123 ≤ invPermX9 d) :
    ((compTable9 H pd idOf W pub χe).getD j #[]).getD d 0 =
      Nock.NockVMROM.Thm54.VclL.HonestTraceX9.trX9 b δ H pd idOf W chalV pubVal ln cnt acc j (invPermX9 d) := by
  rw [compTable9_base H pd idOf W pub χe hj hd hr,
    Nock.NockVMROM.Thm54.VclL.HonestTraceX9.trX9_base b δ H pd idOf W chalV pubVal ln cnt acc j _
      (by rw [Nock.NockVMROM.Thm54.VclL.HonestTraceX9.r0_iff]; unfold invPermX9 at hr ⊢; split_ifs at hr ⊢ <;> omega)]
  rfl

/-! ## K6 → Quad transport of the slot inverse -/

open Nock.TraceGenExe.K6 in
theorem limbVal_readK (f : ℕ → ZMod P) (c : ℕ) :
    Nock.NockVMROM.Thm54.VclL.Compute.LogUp.limbVal powerBasis3 f c = K3.toK (Nock.V1J8.CompX.readK f c) := by
  apply Nock.NockVMROM.Thm54.VclL.Compute.LogUp.limbVal_eq_of_coords
  intro k
  rw [Nock.V1J8.CompX.coord_readK]

theorem gather_eq_kenv (e : Nock.Reified.Env (ZMod P)) :
    Nock.NockVMROM.Thm54.VclL.Compute.TowerD.gatherEnv powerBasis3 e =
      Nock.V1J8.CompX.mapEnvK (Nock.V1J8.CompX.kenv e) := by
  unfold Nock.NockVMROM.Thm54.VclL.Compute.TowerD.gatherEnv Nock.V1J8.CompX.mapEnvK Nock.V1J8.CompX.kenv
  congr 1 <;> funext i <;> exact limbVal_readK _ _

open Nock.NockVMROM.Thm54.T0TowerFP (Q Q.val)

theorem toQ_qE (e : Nock.Reified.Env (ZMod P)) (q : Q (ZMod P)) :
    K6.toQ (Example.qE e q) =
      Q.val deltaF q (Nock.NockVMROM.Thm54.VclL.Compute.TowerD.gatherEnv powerBasis3 e) e := by
  rw [gather_eq_kenv]
  unfold Example.qE K6.toQ Q.val
  simp only [Nock.V1J8.CompX.toK_evalMZ]

theorem toQ_invE9 (e : Nock.Reified.Env (ZMod P)) (k : ℕ) :
    K6.toQ (invE9 e k) =
      HonestSlotX.aVal powerBasis3 deltaF (Nock.NockVMROM.Thm54.VclL.HonestTraceX9.slotAt9 k) e *
        (HonestSlotX.dVal powerBasis3 deltaF (Nock.NockVMROM.Thm54.VclL.HonestTraceX9.slotAt9 k) e)⁻¹ := by
  unfold invE9
  rw [K6.toQ_mul, K6.toQ_inv, toQ_qE, toQ_qE]
  rfl

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ACompute

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ACompute.toQ_invE9
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ACompute.compTable9_getD
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ACompute.compTable9_base
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ACompute.compTable9_eq_trX9_base
