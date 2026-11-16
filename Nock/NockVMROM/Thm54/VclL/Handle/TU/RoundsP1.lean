/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/RoundsP1.lean

 **Trace uniqueness on the P1 fragment: rounds 1 and 2, and the message.**

 * §1 the cell fingerprints `p l r` are determined by the round-0 rows (the validity-served table, at one seed):
 `cell_fps_eq`.
 * §2 generic determination lemmas: inverse columns (`inv_col_unique`), accumulators by induction from the first
 row (`acc_unique`), products / closed forms for the compute walk's `ln` and `cnt` (`prod_rec_unique`,
 `geom_closed`), and the lift from an equal `𝕂`-role to equal base columns (`trace_cols_eq_of_gather`).
 * §3 the terminal pin: a gate `isL·(acc − pub j)` makes the public the accumulator's last value
 (`terminal_pub`, `pub_eq_of_terminal`), at the cell table's validity and export accumulators.
 * §4 the cell table's wire-key export inverse is determined by the round-0 columns (`cell_invHQ_eq`).
 * §5 the message: under `MsgSupp`, the read entries are the terminal values and the balance equations fix
 `ρ 3`, `ρ 4`, `ρS`; so two accepting messages with equal public values and equal claim serials are equal
 (`msg_eq`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1

noncomputable section

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (RowsLe)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)

/-! ## 1. The cell fingerprints -/

section CellFps
variable {q : ℕ} [Fact q.Prime] {Kfp : Type*} [Field Kfp] [Algebra (ZMod q) Kfp]

/-- **The cell fingerprints `p l r` are determined by the round-0 rows.** Two accepted tables at one nonzero
seed with the same round-0 columns (`t.map b0 = t'.map b0`) carry the same `p`, `l`, `r` at rows with the same
round-0 data: each is the fingerprint of the noun the round-0 columns decode to (`row_genuine`). -/
theorem cell_fps_eq (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0) {t t' : List (CellRow q Kfp)}
    {vl vl' : List (VKey Kfp)} (h : TableAccepts z t vl) (h' : TableAccepts z t' vl')
    (hb0 : t.map (·.b0) = t'.map (·.b0)) {c c' : CellRow q Kfp} (hc : c ∈ t) (hc' : c' ∈ t')
    (hbb : c.b0 = c'.b0) : c.p = c'.p ∧ c.l = c'.l ∧ c.r = c'.r := by
  obtain ⟨L, R, hd, hp, hl, hr, -⟩ := row_genuine hq hz h hc
  obtain ⟨L', R', hd', hp', hl', hr', -⟩ := row_genuine hq hz h' hc'
  rw [← hb0, ← hbb, hd] at hd'
  have e := Option.some.inj hd'
  injection e with e1 e2
  subst e1 e2
  exact ⟨hp.trans hp'.symm, hl.trans hl'.symm, hr.trans hr'.symm⟩

end CellFps

/-! ## 2. Generic determination lemmas -/

section Generic

/-- **Inverse columns.** `inv·den = act` with `den ≠ 0` determines `inv`. -/
theorem inv_col_unique {K : Type*} [Field K] {a a' d b : K} (hd : d ≠ 0) (h : a * d = b) (h' : a' * d = b) :
    a = a' := mul_right_cancel₀ hd (h.trans h'.symm)

/-- **Accumulators.** Two sequences with the same first value, the same step terms and the step gate
`a (i+1) − a i = s (i+1)` agree on every row. -/
theorem acc_unique {K : Type*} [AddCommGroup K] (n : ℕ) (a a' s s' : ℕ → K) (h0 : a 0 = s 0) (h0' : a' 0 = s' 0)
    (hs : ∀ i, i < n → s i = s' i) (hst : ∀ i, i + 1 < n → a (i + 1) - a i = s (i + 1))
    (hst' : ∀ i, i + 1 < n → a' (i + 1) - a' i = s' (i + 1)) : ∀ i, i < n → a i = a' i := by
  intro i
  induction i with
  | zero => intro hi; rw [h0, h0', hs 0 hi]
  | succ k ih =>
    intro hi
    have e : a (k + 1) - a k = a' (k + 1) - a' k := by rw [hst k hi, hst' k hi, hs (k + 1) hi]
    rw [ih (by omega)] at e
    exact sub_left_inj.mp e

/-- **Multiplicative recurrences** (the compute walk's `cnt`): `a (i+1) = a i · m i` gives the product form. -/
theorem prod_rec_closed {K : Type*} [CommMonoid K] (n : ℕ) (a : ℕ → K) (m : ℕ → K)
    (hst : ∀ i, i + 1 < n → a (i + 1) = a i * m i) : ∀ i, i < n → a i = a 0 * ∏ j ∈ Finset.range i, m j := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ k ih =>
    intro hi
    rw [hst k hi, ih (by omega), Finset.prod_range_succ, mul_assoc]

/-- Two multiplicative recurrences with the same start and the same factors agree. -/
theorem prod_rec_unique {K : Type*} [CommMonoid K] (n : ℕ) (a a' m : ℕ → K) (h0 : a 0 = a' 0)
    (hst : ∀ i, i + 1 < n → a (i + 1) = a i * m i) (hst' : ∀ i, i + 1 < n → a' (i + 1) = a' i * m i) :
    ∀ i, i < n → a i = a' i := fun i hi => by
  rw [prod_rec_closed n a m hst i hi, prod_rec_closed n a' m hst' i hi, h0]

/-- **Geometric closed form** (the compute walk's `ln = α^{j+1}`): `a (i+1) = c·a i`, `a 0 = c` gives `a i = c^(i+1)`. -/
theorem geom_closed {K : Type*} [CommMonoid K] (n : ℕ) (c : K) (a : ℕ → K) (h0 : a 0 = c)
    (hst : ∀ i, i + 1 < n → a (i + 1) = c * a i) : ∀ i, i < n → a i = c ^ (i + 1) := by
  intro i
  induction i with
  | zero => intro _; simp [h0]
  | succ k ih =>
    intro hi
    rw [hst k hi, ih (by omega), pow_succ' c (k + 1)]

end Generic

/-! ## 2b. From an equal `𝕂`-role to equal base columns -/

section Gather
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **The lift.** If two base-field environments gather to the same `𝕂` value at a role, the `e` base columns of
that role agree (the coordinates of a basis combination are its coefficients). -/
theorem trace_cols_eq_of_gather {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ) (env env' : Env F)
    (idx : ℕ) (h : (gatherEnv b col0 env).trace idx = (gatherEnv b col0 env').trace idx) (k : Fin e) :
    env.trace (col0 .traceCur idx + (k : ℕ)) = env'.trace (col0 .traceCur idx + (k : ℕ)) := by
  have := congrArg (fun x => coord b x k) h
  simpa only [gatherEnv, coord_sum_smul] using this

/-- The same for the next-row columns. -/
theorem traceNext_cols_eq_of_gather {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ) (env env' : Env F)
    (idx : ℕ) (h : (gatherEnv b col0 env).traceNext idx = (gatherEnv b col0 env').traceNext idx) (k : Fin e) :
    env.traceNext (col0 .traceNext idx + (k : ℕ)) = env'.traceNext (col0 .traceNext idx + (k : ℕ)) := by
  have := congrArg (fun x => coord b x k) h
  simpa only [gatherEnv, coord_sum_smul] using this

end Gather

/-! ## 3. The terminal pin -/

section Terminal
variable {F K : Type} [Field F] [Field K] [Algebra F K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

/-- **A terminal gate `isL·(acc − pub j)` at a last row** makes the public the accumulator's last value. -/
theorem terminal_pub (eK : Env K) (eF : Env F) (isL r j : ℕ) (hL : eF.trace isL = 1)
    (h : (QE.scale (cv isL) (QE.sub (QE.var r) (QE.pub j))).ev δF eK eF = 0) :
    eK.pub j = eK.trace r ∧ eK.pub (j + 1) = eK.trace (r + 1) := by
  rw [ev_scale, ev_sub, ev_var, ev_pub] at h
  have hL1 : (cv isL : CoeffExpr F).eval eF = 1 := by simpa [cv, CoeffExpr.eval] using hL
  have hq1 : liftQ (K := K) δF (1 : F) = 1 := by simp [liftQ]
  rw [hL1, hq1, one_mul, Quad.mk_sub, ← Quad.mk_zero' (algebraMap F K δF)] at h
  have := @Quad.mk_injective K _ (algebraMap F K δF) _ (_, _) (0, 0) h
  simp only [Prod.mk.injEq] at this
  exact ⟨(sub_eq_zero.mp this.1).symm, (sub_eq_zero.mp this.2).symm⟩

/-- **The public is determined by the trace**: two environments that satisfy the terminal gate at a last row and
agree on the accumulator role have the same public. -/
theorem pub_eq_of_terminal (eK eK' : Env K) (eF eF' : Env F) (isL r j : ℕ) (hL : eF.trace isL = 1)
    (hL' : eF'.trace isL = 1)
    (h : (QE.scale (cv isL) (QE.sub (QE.var r) (QE.pub j))).ev δF eK eF = 0)
    (h' : (QE.scale (cv isL) (QE.sub (QE.var r) (QE.pub j))).ev δF eK' eF' = 0)
    (h0 : eK.trace r = eK'.trace r) (h1 : eK.trace (r + 1) = eK'.trace (r + 1)) :
    eK.pub j = eK'.pub j ∧ eK.pub (j + 1) = eK'.pub (j + 1) := by
  obtain ⟨a, b⟩ := terminal_pub δF eK eF isL r j hL h
  obtain ⟨a', b'⟩ := terminal_pub δF eK' eF' isL r j hL' h'
  exact ⟨a.trans (h0.trans a'.symm), b.trans (h1.trans b'.symm)⟩

/-- The cell table's validity terminal gate (public `0`) is in its `𝕂′` equation list. -/
theorem cell_vterm_mem : (QE.scale (cv Cell.isL) (QE.sub (QE.var Cell.vAcc) (QE.pub 0)) : QE F) ∈ Cell.qEqs δF := by
  unfold Cell.qEqs; simp

/-- The cell table's export terminal gate (public `2`) is in its `𝕂′` equation list. -/
theorem cell_xterm_mem : (QE.scale (cv Cell.isL) (QE.sub (QE.var Cell.xAcc) (QE.pub 2)) : QE F) ∈ Cell.qEqs δF := by
  unfold Cell.qEqs; simp

end Terminal

/-! ## 4. The cell table's wire-key export inverse -/

section CellInv
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ
open Nock.NockVMROM.Thm54.VclL.Handle.HonestKW (denKeyQW_congr)
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  {Q Q' : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → F[X]}

/-- **The export inverse `invHQ` is determined by the round-0 columns.** Two traces accepted by the cell chip
at one coin and one public vector, agreeing on every round-0 column at a row, agree on the export inverse there:
`inv = den⁻¹` (`cellHQKW_inv`) and `den` reads round-0 columns and coins only (`denKeyQW_congr`). -/
theorem cell_invHQ_eq (hsat : (cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hsat' : (cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies Q') (i : Fin n)
    (ht : ∀ j < 134, (hqkEF b nodes orbit chals pubs Q i).trace j = (hqkEF b nodes orbit chals pubs Q' i).trace j)
    (hn' : ∀ j < 134, (hqkEF b nodes orbit chals pubs Q i).traceNext j =
      (hqkEF b nodes orbit chals pubs Q' i).traceNext j) :
    CellTwinKW.wInvQ δF b nodes orbit chals pubs Q i = CellTwinKW.wInvQ δF b nodes orbit chals pubs Q' i := by
  obtain ⟨-, e⟩ := cellHQKW_inv δF b hn nodes orbit chals pubs Q hsat i
  obtain ⟨-, e'⟩ := cellHQKW_inv δF b hn nodes orbit chals pubs Q' hsat' i
  have hden : CellTwinKW.wDenQ δF b nodes orbit chals pubs Q i = CellTwinKW.wDenQ δF b nodes orbit chals pubs Q' i := by
    exact denKeyQW_congr δF b chals _ _ rfl rfl ht hn'
  rw [e, e', hden]

end CellInv

/-! ## 5. The message -/

section Msg
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (pubMI pubMB pubC)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- Extensionality of the message. -/
theorem msg_ext {X Y : MsgJ8' p K δ} (hm : X.m = Y.m) (hρ : X.ρ = Y.ρ) (hS : X.ρS = Y.ρS)
    (hC : X.pubsC = Y.pubsC) (hW : X.pubsW = Y.pubsW) (hJ : X.pubsJ = Y.pubsJ) (hA : X.pubsA = Y.pubsA)
    (hV : X.pubsV = Y.pubsV) : X = Y := by
  cases X; cases Y
  simp only [MsgJ8'.mk.injEq]
  exact ⟨hm, hρ, hS, hC, hW, hJ, hA, hV⟩

/-- **The message is determined.** Two messages accepted by the J-8 verifier at one layout, claim, coin and
trace, both supported on the read set (`MsgSupp`), with the same claim serials of the cell claim nouns and the
same public values in the read window (the terminal pins: `terminal_pub` and the walk and atom twins, with equal
traces), are equal. The entries outside the window are `0` (E6); `ρ 0, ρ 1, ρ 2` are `0`; `ρ 3`, `ρ 4`, `ρS` are
fixed by the balance equations `hGx`, `hGp`, `hGS`. -/
theorem msg_eq {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M M' : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ}
    (h : AcceptsJ8V δ b Pb Rg c χ M tr r g) (h' : AcceptsJ8V δ b Pb Rg c χ M' tr r g)
    (hs : MsgSupp c M) (hs' : MsgSupp c M')
    (hm : ∀ k, isCellN (claimNoun c k) = true → (M.m k).1 = (M'.m k).1)
    (hC : ∀ j, j < 6 → M.pubsC j = M'.pubsC j) (hW : ∀ j, j < 8 → M.pubsW j = M'.pubsW j)
    (hA : ∀ j, j < 12 → M.pubsA j = M'.pubsA j) : M = M' := by
  have pC : ∀ j, M.pubsC j = M'.pubsC j := fun j => by
    by_cases hj : j < 6
    · exact hC j hj
    · rw [hs.pubsC j (by omega), hs'.pubsC j (by omega)]
  have pW : ∀ j, M.pubsW j = M'.pubsW j := fun j => by
    by_cases hj : j < 8
    · exact hW j hj
    · rw [hs.pubsW j (by omega), hs'.pubsW j (by omega)]
  have pA : ∀ j, M.pubsA j = M'.pubsA j := fun j => by
    by_cases hj : j < 12
    · exact hA j hj
    · rw [hs.pubsA j (by omega), hs'.pubsA j (by omega)]
  have pJ : ∀ j, M.pubsJ j = M'.pubsJ j := fun j => (hs.pubsJ j).trans (hs'.pubsJ j).symm
  have pV : ∀ j, M.pubsV j = M'.pubsV j := fun j => (hs.pubsV j).trans (hs'.pubsV j).symm
  have r3 : M.ρ 3 = M'.ρ 3 := by
    have e1 := h.hGx
    have e2 := h'.hGx
    simp only [pC, pW, pJ] at e1
    exact add_right_cancel (e1.trans e2.symm)
  have r4 : M.ρ 4 = M'.ρ 4 := by
    rw [h.hGp, h'.hGp, pW, pW]
  have rS : M.ρS = M'.ρS := by
    have e1 := h.hGS
    have e2 := h'.hGS
    simp only [pA, pV, pJ] at e1
    exact add_right_cancel (add_right_cancel (e1.trans e2.symm))
  refine msg_ext δ ?_ ?_ rS (funext pC) (funext pW) (funext pJ) (funext pA) (funext pV)
  · funext k
    by_cases hk : isCellN (claimNoun c k) = true
    · exact Prod.ext (hm k hk) ((hs.mRk k).trans (hs'.mRk k).symm)
    · have hf : isCellN (claimNoun c k) = false := by simpa using hk
      exact Prod.ext ((hs.mAtom k hf).trans (hs'.mAtom k hf).symm) ((hs.mRk k).trans (hs'.mRk k).symm)
  · funext i
    match i with
    | ⟨0, _⟩ => exact hs.rho.1.trans hs'.rho.1.symm
    | ⟨1, _⟩ => exact hs.rho.2.1.trans hs'.rho.2.1.symm
    | ⟨2, _⟩ => exact hs.rho.2.2.trans hs'.rho.2.2.symm
    | ⟨3, _⟩ => exact r3
    | ⟨4, _⟩ => exact r4

end Msg

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1.cell_fps_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1.inv_col_unique
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1.acc_unique
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1.prod_rec_unique
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1.geom_closed
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1.trace_cols_eq_of_gather
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1.terminal_pub
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1.pub_eq_of_terminal
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1.cell_vterm_mem
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1.cell_invHQ_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1.msg_eq
