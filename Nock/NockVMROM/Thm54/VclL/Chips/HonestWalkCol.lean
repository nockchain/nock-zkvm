/-
  Nock/NockVMROM/Thm54/VclL/Chips/HonestWalkCol.lean

  **The honest walk chip's columns and gates.**
  The twin of `HonestMemPath` for the walk chip (`WalkChip`, `LayoutW`):

  * `WalkVals F K Q`: the committed content of one walk row (B0 named columns `3…14` and the six
    certificate bits; B1 the four fingerprints `p l r root`; B2 the walk's `ln count acc` (`𝕂`) and the
    five `𝕂′` IO quantities `xInv pInvL pInvR xAcc pAcc`);
  * `walkCol kr` (column `2` is the root mask `[i < kr]`), `honestWalkQ` (the `132`-column interpolated
    trace), the environment lemmas;
  * `walk_base_gates_hold` (the `19` base gates, given `WalkBaseFacts`);
  * `walk_qEqs_hold` / `walk_mixed_gates_hold` (the `12` `𝕂′` equations / `31` mixed gates, given
    `WalkMixedFacts`).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemAccept
import Nock.NockVMROM.Thm54.VclL.Chips.WalkAcceptW

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL
open Module
open scoped Polynomial

noncomputable section

/-- **The committed content of one walk row.** -/
structure WalkVals (F K Q : Type) where
  idx : F
  pre : F
  ridx : F
  len : F
  cL : F
  cR : F
  e : F
  mL : F
  mR : F
  q : F
  qinv : F
  u : F
  bit : ℕ → F
  p : ComputeTable.FP Q
  l : ComputeTable.FP Q
  r : ComputeTable.FP Q
  root : ComputeTable.FP Q
  ln : K
  cnt : K
  acc : K
  xInv : Q
  pInvL : Q
  pInvR : Q
  xAcc : Q
  pAcc : Q

namespace WalkVals
variable {F K Q : Type} [Zero F] [One F]

/-- The named base columns `2 … 14` (column `2` is the root mask `[i < kr]`). -/
def named (v : WalkVals F K Q) (kr i : ℕ) : ℕ → F
  | 2 => if i < kr then 1 else 0
  | 3 => v.idx | 4 => v.pre | 5 => v.ridx | 6 => v.len | 7 => v.cL | 8 => v.cR | 9 => v.e
  | 10 => v.mL | 11 => v.mR | 12 => v.q | 13 => v.qinv | 14 => v.u
  | _ => 0

/-- The base column `j` (`2 ≤ j < 21`; `15 …` are the certificate bits). -/
def base (v : WalkVals F K Q) (kr i j : ℕ) : F :=
  if j < 15 then v.named kr i j else v.bit (j - 15)

/-- The fingerprint `𝕂′` slots (`p l r root`, three each). -/
def fpSlot (v : WalkVals F K Q) : ℕ → Q
  | 0 => v.p.size | 1 => v.p.dyck | 2 => v.p.leaf
  | 3 => v.l.size | 4 => v.l.dyck | 5 => v.l.leaf
  | 6 => v.r.size | 7 => v.r.dyck | 8 => v.r.leaf
  | 9 => v.root.size | 10 => v.root.dyck | _ => v.root.leaf

/-- The IO `𝕂′` slots (`xInv pInvL pInvR xAcc pAcc`). -/
def ioSlot (v : WalkVals F K Q) : ℕ → Q
  | 0 => v.xInv | 1 => v.pInvL | 2 => v.pInvR | 3 => v.xAcc | _ => v.pAcc

end WalkVals

section Cols
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) (kr : ℕ)

/-- The `𝕂`-role `ρ` of a walk row (`LayoutW`: roles `0…23` the four fingerprints, `24 25 26`
`ln count acc`, `27…36` the five `𝕂′` IO quantities). -/
def wroleVal (v : WalkVals F K (Quad (algebraMap F K δF))) (ρ : ℕ) : K :=
  if ρ < 24 then
    (if ρ % 2 = 0 then Quad.re _ (v.fpSlot (ρ / 2)) else Quad.im _ (v.fpSlot (ρ / 2)))
  else if ρ = 24 then v.ln else if ρ = 25 then v.cnt else if ρ = 26 then v.acc
  else if (ρ - 27) % 2 = 0 then Quad.re _ (v.ioSlot ((ρ - 27) / 2))
  else Quad.im _ (v.ioSlot ((ρ - 27) / 2))

/-- **The walk chip's column function**: base columns `2 … 20`, `𝕂`-role `ρ` at `21 + 3ρ + k`. -/
def walkCol {n : ℕ} (vals : Fin n → WalkVals F K (Quad (algebraMap F K δF))) (j : ℕ) (i : Fin n) : F :=
  if j < 21 then (vals i).base kr i j
  else coord b (wroleVal δF (vals i) ((j - 21) / 3)) ⟨(j - 21) % 3, Nat.mod_lt _ (by norm_num)⟩

end Cols

section Env
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) (kr : ℕ) {n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (ω : F) (chals pubs : ℕ → K)
  (vals : Fin n → WalkVals F K (Quad (algebraMap F K δF)))

/-- The honest walk trace. -/
abbrev honestWalkQ : Fin 132 → F[X] := honestQ hn nodes (walkCol δF b kr vals) 132

abbrev walkEFh (i : Fin n) : Env F :=
  Reify.envOfTrace (honestWalkQ δF b kr hn nodes vals) ω (nodes i) (slotVal b 21 chals) (slotVal b 21 pubs)

abbrev walkEKh (i : Fin n) : Env K :=
  gatherEnv b ((walkTemplate δF kr).col0 3) (walkEFh δF b kr hn nodes ω chals pubs vals i)

theorem walkEFh_base (hinj : Function.Injective nodes) (i : Fin n) {j : ℕ} (h2 : 2 ≤ j) (hj : j < 21) :
    (walkEFh δF b kr hn nodes ω chals pubs vals i).trace j = (vals i).base kr i j := by
  rw [env_trace hn nodes hinj _ ω _ _ i (show j < 132 by omega)]
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  unfold fullCol walkCol
  rw [if_neg h0, if_neg h1, if_pos hj]

/-- Under adjacency the next row of the honest environment is row `i + 1` (every column). -/
theorem walkEFh_next (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (j : ℕ) :
    (walkEFh δF b kr hn nodes ω chals pubs vals i).traceNext j =
      (walkEFh δF b kr hn nodes ω chals pubs vals ⟨(i : ℕ) + 1, hi⟩).trace j := by
  simp only [Reify.envOfTrace]
  rw [hadj i hi, mul_comm]

theorem walkEFh_next_base (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) {j : ℕ} (h2 : 2 ≤ j) (hj : j < 21) :
    (walkEFh δF b kr hn nodes ω chals pubs vals i).traceNext j =
      (vals ⟨(i : ℕ) + 1, hi⟩).base kr ((i : ℕ) + 1) j := by
  rw [walkEFh_next δF b kr hn nodes ω chals pubs vals hinj hadj i hi,
    walkEFh_base δF b kr hn nodes ω chals pubs vals hinj _ h2 hj]

theorem walkEFh_mask0 (hinj : Function.Injective nodes) (i : Fin n) :
    (walkEFh δF b kr hn nodes ω chals pubs vals i).trace 0 = if (i : ℕ) = 0 then 1 else 0 := by
  rw [env_trace hn nodes hinj _ ω _ _ i (show 0 < 132 by omega)]
  simp [fullCol]

theorem walkEFh_mask1 (hinj : Function.Injective nodes) (i : Fin n) :
    (walkEFh δF b kr hn nodes ω chals pubs vals i).trace 1 =
      if i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩ then 1 else 0 := by
  rw [env_trace hn nodes hinj _ ω _ _ i (show 1 < 132 by omega)]
  simp [fullCol]

theorem walk_col0 (r : ℕ) (kind : VarKind) : (walkTemplate δF kr).col0 3 kind r = 21 + 3 * r := by
  simp [ChipTemplate.col0, walkTemplate_baseCols]

theorem walkEKh_trace (hinj : Function.Injective nodes) (i : Fin n) {r : ℕ} (hr : r < 37) :
    (walkEKh δF b kr hn nodes ω chals pubs vals i).trace r = wroleVal δF (vals i) r := by
  refine gather_trace b _ _ r _ fun k => ?_
  rw [walk_col0, env_trace hn nodes hinj _ ω _ _ i (show 21 + 3 * r + (k : ℕ) < 132 by have := k.isLt; omega)]
  have h1 : (21 + 3 * r + (k : ℕ) - 21) / 3 = r := by have := k.isLt; omega
  have h2 : (21 + 3 * r + (k : ℕ) - 21) % 3 = (k : ℕ) := by have := k.isLt; omega
  have h0 : (21 + 3 * r + (k : ℕ)) ≠ 0 := by omega
  have h1' : (21 + 3 * r + (k : ℕ)) ≠ 1 := by omega
  have h3 : ¬ (21 + 3 * r + (k : ℕ)) < 21 := by omega
  unfold fullCol walkCol
  rw [if_neg h0, if_neg h1', if_neg h3, h1]
  exact congrArg (coord b _) (Fin.ext h2)

/-- The gathered `𝕂` environment's next row is row `i + 1`'s (every role). -/
theorem walkEKh_next (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (r : ℕ) :
    (walkEKh δF b kr hn nodes ω chals pubs vals i).traceNext r =
      (walkEKh δF b kr hn nodes ω chals pubs vals ⟨(i : ℕ) + 1, hi⟩).trace r := by
  simp only [gatherEnv, ChipTemplate.col0, walkEFh_next δF b kr hn nodes ω chals pubs vals hinj hadj i hi]

theorem walkEKh_ev_fp (hinj : Function.Injective nodes) (i : Fin n) {s : ℕ} (hs : s < 12) :
    (QE.var (2 * s) : QE F).ev δF (walkEKh δF b kr hn nodes ω chals pubs vals i)
        (walkEFh δF b kr hn nodes ω chals pubs vals i) = (vals i).fpSlot s := by
  rw [ev_var, walkEKh_trace δF b kr hn nodes ω chals pubs vals hinj i (by omega),
    walkEKh_trace δF b kr hn nodes ω chals pubs vals hinj i (show 2 * s + 1 < 37 by omega)]
  have e0 : 2 * s < 24 := by omega
  have e0' : 2 * s + 1 < 24 := by omega
  have e1 : (2 * s) % 2 = 0 := by omega
  have e2 : (2 * s) / 2 = s := by omega
  have e3 : (2 * s + 1) % 2 ≠ 0 := by omega
  have e4 : (2 * s + 1) / 2 = s := by omega
  simp only [wroleVal, e0, e0', e1, e2, e3, e4, if_true, if_false]
  exact Quad.mk_re_im _ _

theorem walkEKh_ev_io (hinj : Function.Injective nodes) (i : Fin n) {s : ℕ} (hs : s < 5) :
    (QE.var (27 + 2 * s) : QE F).ev δF (walkEKh δF b kr hn nodes ω chals pubs vals i)
        (walkEFh δF b kr hn nodes ω chals pubs vals i) = (vals i).ioSlot s := by
  rw [ev_var, walkEKh_trace δF b kr hn nodes ω chals pubs vals hinj i (by omega),
    walkEKh_trace δF b kr hn nodes ω chals pubs vals hinj i (show 27 + 2 * s + 1 < 37 by omega)]
  have a0 : ¬ 27 + 2 * s < 24 := by omega
  have a1 : 27 + 2 * s ≠ 24 := by omega
  have a2 : 27 + 2 * s ≠ 25 := by omega
  have a3 : 27 + 2 * s ≠ 26 := by omega
  have b0 : ¬ 27 + 2 * s + 1 < 24 := by omega
  have b1 : 27 + 2 * s + 1 ≠ 24 := by omega
  have b2 : 27 + 2 * s + 1 ≠ 25 := by omega
  have b3 : 27 + 2 * s + 1 ≠ 26 := by omega
  have e1 : (27 + 2 * s - 27) % 2 = 0 := by omega
  have e2 : (27 + 2 * s - 27) / 2 = s := by omega
  have e3 : (27 + 2 * s + 1 - 27) % 2 ≠ 0 := by omega
  have e4 : (27 + 2 * s + 1 - 27) / 2 = s := by omega
  simp only [wroleVal, a0, a1, a2, a3, b0, b1, b2, b3, e1, e2, e3, e4, if_true, if_false]
  exact Quad.mk_re_im _ _

theorem walkEKh_chal (i : Fin n) : (walkEKh δF b kr hn nodes ω chals pubs vals i).chal = chals :=
  funext fun j => gather_chal_walk δF kr b chals _ rfl j

theorem walkEKh_pub (i : Fin n) (j : ℕ) : (walkEKh δF b kr hn nodes ω chals pubs vals i).pub j = pubs j :=
  gather_pub_walk δF kr b pubs _ rfl j

theorem walkEKh_ln (hinj : Function.Injective nodes) (i : Fin n) :
    (walkEKh δF b kr hn nodes ω chals pubs vals i).trace WChip.lnR = (vals i).ln := by
  rw [walkEKh_trace δF b kr hn nodes ω chals pubs vals hinj i (by decide)]; rfl
theorem walkEKh_cnt (hinj : Function.Injective nodes) (i : Fin n) :
    (walkEKh δF b kr hn nodes ω chals pubs vals i).trace WChip.cntR = (vals i).cnt := by
  rw [walkEKh_trace δF b kr hn nodes ω chals pubs vals hinj i (by decide)]; rfl
theorem walkEKh_acc (hinj : Function.Injective nodes) (i : Fin n) :
    (walkEKh δF b kr hn nodes ω chals pubs vals i).trace WChip.accR = (vals i).acc := by
  rw [walkEKh_trace δF b kr hn nodes ω chals pubs vals hinj i (by decide)]; rfl

/-- The fingerprints at roles `pR lR rR rootR`. -/
theorem walkEKh_fps (hinj : Function.Injective nodes) (i : Fin n) :
    (QFP.var WChip.pR : QFP F).ev δF (walkEKh δF b kr hn nodes ω chals pubs vals i)
        (walkEFh δF b kr hn nodes ω chals pubs vals i) = (vals i).p ∧
      (QFP.var WChip.lR : QFP F).ev δF (walkEKh δF b kr hn nodes ω chals pubs vals i)
        (walkEFh δF b kr hn nodes ω chals pubs vals i) = (vals i).l ∧
      (QFP.var WChip.rR : QFP F).ev δF (walkEKh δF b kr hn nodes ω chals pubs vals i)
        (walkEFh δF b kr hn nodes ω chals pubs vals i) = (vals i).r ∧
      (QFP.var WChip.rootR : QFP F).ev δF (walkEKh δF b kr hn nodes ω chals pubs vals i)
        (walkEFh δF b kr hn nodes ω chals pubs vals i) = (vals i).root := by
  have h := fun (s : ℕ) (hs : s < 12) => walkEKh_ev_fp δF b kr hn nodes ω chals pubs vals hinj i hs
  have h0 := h 0 (by norm_num); have h1 := h 1 (by norm_num); have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num); have h4 := h 4 (by norm_num); have h5 := h 5 (by norm_num)
  have h6 := h 6 (by norm_num); have h7 := h 7 (by norm_num); have h8 := h 8 (by norm_num)
  have h9 := h 9 (by norm_num); have h10 := h 10 (by norm_num); have h11 := h 11 (by norm_num)
  simp only [Nat.mul_zero, Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [QFP.ev, QFP.var, WChip.pR, WChip.lR, WChip.rR, WChip.rootR, Nat.reduceAdd, zero_add,
      h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11] <;> rfl

end Env

section BaseGates
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) (kr : ℕ) {n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (ω : F) (chals pubs : ℕ → K)
  (vals : Fin n → WalkVals F K (Quad (algebraMap F K δF)))

/-- **The row-level facts the `19` walk base gates encode** (at row `i`, masks resolved). -/
structure WalkBaseFacts {F K Q : Type} [Field F] (kr : ℕ) {n : ℕ} (vals : Fin n → WalkVals F K Q)
    (i : Fin n) : Prop where
  cL_bool : (vals i).cL * ((vals i).cL - 1) = 0
  cR_bool : (vals i).cR * ((vals i).cR - 1) = 0
  e_eq : (vals i).e = (vals i).cL * (vals i).cR
  u_eq : (vals i).u = (vals i).bit 1 * (vals i).bit 2
  excl : (vals i).u * (vals i).bit 3 * ((vals i).bit 4 * (vals i).bit 5) = 0
  cert : (vals i).len + ∑ k ∈ Finset.range 6, (2 : F) ^ k * (vals i).bit k = 61
  root_pre : (i : ℕ) < kr → (vals i).pre = 1
  root_len : (i : ℕ) < kr → (vals i).len = 0
  root_ridx : (i : ℕ) < kr → (vals i).ridx = (vals i).idx
  q_first : (i : ℕ) = 0 → (vals i).q + 1 = (kr : F) + (vals i).cL + (vals i).cR
  q_step : ∀ hi : (i : ℕ) + 1 < n,
    (vals ⟨(i : ℕ) + 1, hi⟩).q + 1 = (vals i).q + (vals ⟨(i : ℕ) + 1, hi⟩).cL + (vals ⟨(i : ℕ) + 1, hi⟩).cR
  q_inv : (i : ℕ) + 1 < n → (vals i).q * (vals i).qinv = 1
  q_last : (i : ℕ) + 1 = n → (vals i).q = 0
  bit_bool : ∀ k < 6, (vals i).bit k * ((vals i).bit k - 1) = 0

theorem walk_hiff (i : Fin n) :
    i = (⟨n - 1, Nat.sub_lt hn (by omega)⟩ : Fin n) ↔ (i : ℕ) + 1 = n := by
  constructor
  · intro h; rw [h]; simp; omega
  · intro h; apply Fin.ext; simp; omega

/-- **The `19` walk base gates vanish at the honest environment of row `i`.** -/
theorem walk_base_gates_hold (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hf : WalkBaseFacts kr vals i) :
    ∀ g ∈ WChip.baseGates (F := F) kr,
      g.eval (walkEFh δF b kr hn nodes ω chals pubs vals i) = 0 := by
  have hb : ∀ j, 2 ≤ j → j < 21 → (walkEFh δF b kr hn nodes ω chals pubs vals i).trace j =
      (vals i).base kr i j :=
    fun j h2 hj => walkEFh_base δF b kr hn nodes ω chals pubs vals hinj i h2 hj
  have hbn : ∀ hi : (i : ℕ) + 1 < n, ∀ j, 2 ≤ j → j < 21 →
      (walkEFh δF b kr hn nodes ω chals pubs vals i).traceNext j =
        (vals ⟨(i : ℕ) + 1, hi⟩).base kr ((i : ℕ) + 1) j :=
    fun hi j h2 hj => walkEFh_next_base δF b kr hn nodes ω chals pubs vals hinj hadj i hi h2 hj
  have m0 := walkEFh_mask0 δF b kr hn nodes ω chals pubs vals hinj i
  have m1 := walkEFh_mask1 δF b kr hn nodes ω chals pubs vals hinj i
  set E := walkEFh δF b kr hn nodes ω chals pubs vals i with hE
  have t2 : E.trace 2 = if (i : ℕ) < kr then 1 else 0 := by rw [hb 2 le_rfl (by norm_num)]; rfl
  have t3 : E.trace 3 = (vals i).idx := by rw [hb 3 (by norm_num) (by norm_num)]; rfl
  have t4 : E.trace 4 = (vals i).pre := by rw [hb 4 (by norm_num) (by norm_num)]; rfl
  have t5 : E.trace 5 = (vals i).ridx := by rw [hb 5 (by norm_num) (by norm_num)]; rfl
  have t6 : E.trace 6 = (vals i).len := by rw [hb 6 (by norm_num) (by norm_num)]; rfl
  have t7 : E.trace 7 = (vals i).cL := by rw [hb 7 (by norm_num) (by norm_num)]; rfl
  have t8 : E.trace 8 = (vals i).cR := by rw [hb 8 (by norm_num) (by norm_num)]; rfl
  have t9 : E.trace 9 = (vals i).e := by rw [hb 9 (by norm_num) (by norm_num)]; rfl
  have t12 : E.trace 12 = (vals i).q := by rw [hb 12 (by norm_num) (by norm_num)]; rfl
  have t13 : E.trace 13 = (vals i).qinv := by rw [hb 13 (by norm_num) (by norm_num)]; rfl
  have t14 : E.trace 14 = (vals i).u := by rw [hb 14 (by norm_num) (by norm_num)]; rfl
  have tbit : ∀ k, k < 6 → E.trace (15 + k) = (vals i).bit k := fun k hk => by
    rw [hb (15 + k) (by omega) (by omega)]
    simp only [WalkVals.base, if_neg (show ¬ 15 + k < 15 by omega), Nat.add_sub_cancel_left]
  have hiff := walk_hiff hn i
  intro g hg
  simp only [WChip.baseGates, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hg
  rcases hg with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    ⟨k, hk, rfl⟩
  · simp only [CoeffExpr.eval, cv, WChip.cL, t7]; exact hf.cL_bool
  · simp only [CoeffExpr.eval, cv, WChip.cR, t8]; exact hf.cR_bool
  · simp only [CoeffExpr.eval, cv, WChip.e, WChip.cL, WChip.cR, t7, t8, t9, hf.e_eq, sub_self]
  · simp only [CoeffExpr.eval, cv, WChip.bt, WChip.u, WChip.bit0, t14]
    rw [tbit 1 (by norm_num), tbit 2 (by norm_num), hf.u_eq, sub_self]
  · simp only [CoeffExpr.eval, cv, WChip.bt, WChip.u, WChip.bit0, t14]
    rw [tbit 3 (by norm_num), tbit 4 (by norm_num), tbit 5 (by norm_num)]
    exact hf.excl
  · simp only [CoeffExpr.eval, cv, WChip.len, WChip.bit0, eval_bitSum, t6]
    have : ∀ k ∈ Finset.range 6, (2 : F) ^ k * E.trace (15 + k) = (2 : F) ^ k * (vals i).bit k :=
      fun k hk => by rw [tbit k (Finset.mem_range.mp hk)]
    rw [Finset.sum_congr rfl this, hf.cert, sub_self]
  · simp only [CoeffExpr.eval, cv, WChip.rM, WChip.pre, t2, t4]
    by_cases hk : (i : ℕ) < kr
    · rw [if_pos hk, hf.root_pre hk]; ring
    · rw [if_neg hk]; ring
  · simp only [CoeffExpr.eval, cv, WChip.rM, WChip.len, t2, t6]
    by_cases hk : (i : ℕ) < kr
    · rw [if_pos hk, hf.root_len hk]; ring
    · rw [if_neg hk]; ring
  · simp only [CoeffExpr.eval, cv, WChip.rM, WChip.ridx, WChip.idx, t2, t5, t3]
    by_cases hk : (i : ℕ) < kr
    · rw [if_pos hk, hf.root_ridx hk]; ring
    · rw [if_neg hk]; ring
  · simp only [CoeffExpr.eval, cv, WChip.isF, WChip.q, WChip.cL, WChip.cR, t12, t7, t8, m0]
    by_cases h0 : (i : ℕ) = 0
    · rw [if_pos h0]; linear_combination hf.q_first h0
    · rw [if_neg h0]; ring
  · simp only [CoeffExpr.eval, cv, nv, notE, WChip.isL, WChip.q, WChip.cL, WChip.cR, t12, m1]
    by_cases hl : (i : ℕ) + 1 = n
    · rw [if_pos (hiff.mpr hl)]; ring
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      rw [if_neg (fun h => hl (hiff.mp h)), hbn hi 12 (by norm_num) (by norm_num),
        hbn hi 7 (by norm_num) (by norm_num), hbn hi 8 (by norm_num) (by norm_num)]
      simp only [WalkVals.base, WalkVals.named, show (12 : ℕ) < 15 by norm_num,
        show (7 : ℕ) < 15 by norm_num, show (8 : ℕ) < 15 by norm_num, if_true]
      linear_combination hf.q_step hi
  · simp only [CoeffExpr.eval, cv, notE, WChip.isL, WChip.q, WChip.qinv, t12, t13, m1]
    by_cases hl : (i : ℕ) + 1 = n
    · rw [if_pos (hiff.mpr hl)]; ring
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      rw [if_neg (fun h => hl (hiff.mp h)), hf.q_inv hi]; ring
  · simp only [CoeffExpr.eval, cv, WChip.isL, WChip.q, t12, m1]
    by_cases hl : (i : ℕ) + 1 = n
    · rw [if_pos (hiff.mpr hl), hf.q_last hl]; ring
    · rw [if_neg (fun h => hl (hiff.mp h))]; ring
  · simp only [CoeffExpr.eval, cv, WChip.bt, WChip.bit0]
    rw [tbit k hk]
    exact hf.bit_bool k hk

end BaseGates

section KGates
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) (kr : ℕ) {n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (ω : F) (chals pubs : ℕ → K)
  (vals : Fin n → WalkVals F K (Quad (algebraMap F K δF)))

def lblV (v : WalkVals F K (Quad (algebraMap F K δF))) : WalkVCL.LT (ringChar F) (Quad (algebraMap F K δF)) :=
  ((decide (v.cL = 1), decide (v.cR = 1)), ⟨v.p, zq v.pre, v.root, zq v.ridx, zq v.len⟩)

/-- The export key a walk row's values consume. -/
def keyV (v : WalkVals F K (Quad (algebraMap F K δF))) : XKey (Quad (algebraMap F K δF)) :=
  (v.p, v.l, v.r, natOf v.idx)

/-- The row RLC `RLC^γ(enc(lbl))`. -/
def curV (γ : K) (v : WalkVals F K (Quad (algebraMap F K δF))) : K :=
  Nock.Walk.rlc γ (WalkVCL.enc (algebraMap F K δF) (lblV δF v))

/-- The in-gate child sum `Σ_{l ≤ fo} α^l RLC^γ(enc(child_l))`. -/
def ccV (α γ : K) (v : WalkVals F K (Quad (algebraMap F K δF))) : K :=
  ∑ l ∈ Finset.Icc 1 (WalkVCL.fanout (lblV δF v).1), α ^ l *
    Nock.Walk.rlc γ (WalkVCL.enc (algebraMap F K δF)
      ((((false, false), childDT (keyV δF v) (sideOf (lblV δF v).1 l) (lblV δF v).2)) :
        WalkVCL.LT (ringChar F) (Quad (algebraMap F K δF))))

theorem walk_lblRow (hinj : Function.Injective nodes) (i : Fin n) :
    lblRow δF (walkEKh δF b kr hn nodes ω chals pubs vals i) (walkEFh δF b kr hn nodes ω chals pubs vals i) =
      lblV δF (vals i) := by
  obtain ⟨hp, -, -, hr⟩ := walkEKh_fps δF b kr hn nodes ω chals pubs vals hinj i
  have hb := fun (j : ℕ) (h2 : 2 ≤ j) (hj : j < 21) =>
    walkEFh_base δF b kr hn nodes ω chals pubs vals hinj i h2 hj
  simp only [lblRow, lblV, hp, hr, WChip.cL, WChip.cR, WChip.pre, WChip.ridx, WChip.len,
    hb 7 (by norm_num) (by norm_num), hb 8 (by norm_num) (by norm_num), hb 4 (by norm_num) (by norm_num),
    hb 5 (by norm_num) (by norm_num), hb 6 (by norm_num) (by norm_num)]
  rfl

theorem walk_keyRow (hinj : Function.Injective nodes) (i : Fin n) :
    keyRow δF (walkEKh δF b kr hn nodes ω chals pubs vals i) (walkEFh δF b kr hn nodes ω chals pubs vals i) =
      keyV δF (vals i) := by
  obtain ⟨hp, hl, hr, -⟩ := walkEKh_fps δF b kr hn nodes ω chals pubs vals hinj i
  simp only [keyRow, keyV, hp, hl, hr, WChip.idx,
    walkEFh_base δF b kr hn nodes ω chals pubs vals hinj i (show 2 ≤ 3 by norm_num) (show 3 < 21 by norm_num)]
  rfl

variable (hF : GeneratedField.PrimeFieldElems F)
include hF

theorem afo_cc_V {k : VarKind} {bc : ℕ → CoeffExpr F} {eK eK' : Env K} {eF eF' : Env F}
    (V : View k bc eK eK' eF eF') (v : WalkVals F K (Quad (algebraMap F K δF)))
    (hl : lblRow δF eK' eF' = lblV δF v) (hk : keyRow δF eK' eF' = keyV δF v)
    (bL : eF'.trace WChip.cL = 0 ∨ eF'.trace WChip.cL = 1)
    (bR : eF'.trace WChip.cR = 0 ∨ eF'.trace WChip.cR = 1)
    (he : eF'.trace WChip.e = eF'.trace WChip.cL * eF'.trace WChip.cR) :
    (WChip.afoW bc).eval eK eF = eK.chal 0 ^ WalkVCL.fanout (lblV δF v).1 ∧
      (WChip.ccW k bc).eval eK eF = ccV δF (eK.chal 0) (eK.chal 1) v := by
  obtain ⟨h1, h2⟩ := afo_cc_row δF hF V bL bR he
  rw [hl] at h1
  refine ⟨h1, ?_⟩
  rw [h2]
  simp only [childLbl, hl, hk, ccV]

theorem cur_V {k : VarKind} {bc : ℕ → CoeffExpr F} {eK eK' : Env K} {eF eF' : Env F}
    (V : View k bc eK eK' eF eF') (v : WalkVals F K (Quad (algebraMap F K δF)))
    (hl : lblRow δF eK' eF' = lblV δF v) :
    (WChip.curW k bc).eval eK eF = curV δF (eK.chal 1) v := by
  rw [cur_row δF hF V, hl]; rfl

omit hF in
/-- **The semantic content of the `7` walk `𝕂`-gates at row `i`** (`α = χ₀`, `γ = χ₁`). -/
structure WalkKFacts (α γ : K) (i : Fin n) : Prop where
  ln_first : (i : ℕ) = 0 → (vals i).ln = α
  ln_step : ∀ hi : (i : ℕ) + 1 < n, (vals ⟨(i : ℕ) + 1, hi⟩).ln = α * (vals i).ln
  cnt_first : (i : ℕ) = 0 → (vals i).cnt = α ^ kr * α ^ WalkVCL.fanout (lblV δF (vals i)).1
  cnt_step : ∀ hi : (i : ℕ) + 1 < n,
    (vals ⟨(i : ℕ) + 1, hi⟩).cnt = (vals i).cnt * α ^ WalkVCL.fanout (lblV δF (vals ⟨(i : ℕ) + 1, hi⟩)).1
  acc_first : (i : ℕ) = 0 → (vals i).acc = α ^ kr * ccV δF α γ (vals i)
  acc_step : ∀ hi : (i : ℕ) + 1 < n,
    algebraMap F K (1 - if (i : ℕ) + 1 < kr then 1 else 0) * (vals ⟨(i : ℕ) + 1, hi⟩).ln *
        curV δF γ (vals ⟨(i : ℕ) + 1, hi⟩) + ((vals ⟨(i : ℕ) + 1, hi⟩).acc - (vals i).acc) =
      (vals i).cnt * ccV δF α γ (vals ⟨(i : ℕ) + 1, hi⟩)
  acc_last : (i : ℕ) + 1 = n → (vals i).acc = 0

omit hF in
theorem walk_bits_of_facts {i : Fin n} (hf : WalkBaseFacts kr vals i) (hinj : Function.Injective nodes) :
    ((walkEFh δF b kr hn nodes ω chals pubs vals i).trace WChip.cL = 0 ∨
        (walkEFh δF b kr hn nodes ω chals pubs vals i).trace WChip.cL = 1) ∧
      ((walkEFh δF b kr hn nodes ω chals pubs vals i).trace WChip.cR = 0 ∨
        (walkEFh δF b kr hn nodes ω chals pubs vals i).trace WChip.cR = 1) ∧
      (walkEFh δF b kr hn nodes ω chals pubs vals i).trace WChip.e =
        (walkEFh δF b kr hn nodes ω chals pubs vals i).trace WChip.cL *
          (walkEFh δF b kr hn nodes ω chals pubs vals i).trace WChip.cR := by
  have hb := fun (j : ℕ) (h2 : 2 ≤ j) (hj : j < 21) =>
    walkEFh_base δF b kr hn nodes ω chals pubs vals hinj i h2 hj
  simp only [WChip.cL, WChip.cR, WChip.e, hb 7 (by norm_num) (by norm_num), hb 8 (by norm_num) (by norm_num),
    hb 9 (by norm_num) (by norm_num)]
  exact ⟨bool_val hf.cL_bool, bool_val hf.cR_bool, hf.e_eq⟩

/-- **The `7` walk `𝕂`-gates vanish at the honest environment of row `i`.** -/
theorem walk_kgates_hold (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hb : ∀ j, WalkBaseFacts kr vals j) (hk : WalkKFacts δF kr vals (chals 0) (chals 1) i) :
    ∀ g ∈ WChip.walkGates (F := F) kr,
      g.eval (walkEKh δF b kr hn nodes ω chals pubs vals i) (walkEFh δF b kr hn nodes ω chals pubs vals i) = 0 := by
  set eK := walkEKh δF b kr hn nodes ω chals pubs vals i with heK
  set eF := walkEFh δF b kr hn nodes ω chals pubs vals i with heF
  have hch : ∀ c, eK.chal c = chals c := fun c => by rw [heK, walkEKh_chal]
  have m0 := walkEFh_mask0 δF b kr hn nodes ω chals pubs vals hinj i
  have m1 := walkEFh_mask1 δF b kr hn nodes ω chals pubs vals hinj i
  rw [← heF] at m0 m1
  have hiff := walk_hiff hn i
  have tln := walkEKh_ln δF b kr hn nodes ω chals pubs vals hinj i
  have tcnt := walkEKh_cnt δF b kr hn nodes ω chals pubs vals hinj i
  have tacc := walkEKh_acc δF b kr hn nodes ω chals pubs vals hinj i
  rw [← heK] at tln tcnt tacc
  obtain ⟨bL, bR, he⟩ := walk_bits_of_facts δF b kr hn nodes ω chals pubs vals (hb i) hinj
  rw [← heF] at bL bR he
  have ccC := afo_cc_V δF hF (view_cur eK eF) (vals i)
    (walk_lblRow δF b kr hn nodes ω chals pubs vals hinj i)
    (walk_keyRow δF b kr hn nodes ω chals pubs vals hinj i) bL bR he
  rw [hch, hch] at ccC
  -- the next row
  have hnext : ∀ hi : (i : ℕ) + 1 < n,
      (WChip.afoW nv).eval eK eF = chals 0 ^ WalkVCL.fanout (lblV δF (vals ⟨(i : ℕ) + 1, hi⟩)).1 ∧
      (WChip.ccW .traceNext nv).eval eK eF = ccV δF (chals 0) (chals 1) (vals ⟨(i : ℕ) + 1, hi⟩) ∧
      (WChip.curW .traceNext nv).eval eK eF = curV δF (chals 1) (vals ⟨(i : ℕ) + 1, hi⟩) ∧
      eK.traceNext WChip.lnR = (vals ⟨(i : ℕ) + 1, hi⟩).ln ∧
      eK.traceNext WChip.cntR = (vals ⟨(i : ℕ) + 1, hi⟩).cnt ∧
      eK.traceNext WChip.accR = (vals ⟨(i : ℕ) + 1, hi⟩).acc ∧
      eF.traceNext WChip.rM = if (i : ℕ) + 1 < kr then 1 else 0 := by
    intro hi
    have V : View .traceNext nv eK (walkEKh δF b kr hn nodes ω chals pubs vals ⟨(i : ℕ) + 1, hi⟩) eF
        (walkEFh δF b kr hn nodes ω chals pubs vals ⟨(i : ℕ) + 1, hi⟩) :=
      ⟨fun r => walkEKh_next δF b kr hn nodes ω chals pubs vals hinj hadj i hi r,
        fun j => walkEFh_next δF b kr hn nodes ω chals pubs vals hinj hadj i hi j⟩
    obtain ⟨bL', bR', he'⟩ := walk_bits_of_facts δF b kr hn nodes ω chals pubs vals
      (i := ⟨(i : ℕ) + 1, hi⟩) (hb _) hinj
    have hl' := walk_lblRow δF b kr hn nodes ω chals pubs vals hinj ⟨(i : ℕ) + 1, hi⟩
    have cc' := afo_cc_V δF hF V (vals ⟨(i : ℕ) + 1, hi⟩) hl'
      (walk_keyRow δF b kr hn nodes ω chals pubs vals hinj ⟨(i : ℕ) + 1, hi⟩) bL' bR' he'
    rw [hch, hch] at cc'
    have cu := cur_V δF hF V (vals ⟨(i : ℕ) + 1, hi⟩) hl'
    rw [hch] at cu
    refine ⟨cc'.1, cc'.2, cu, ?_, ?_, ?_, ?_⟩
    · rw [walkEKh_next δF b kr hn nodes ω chals pubs vals hinj hadj i hi]
      exact walkEKh_ln δF b kr hn nodes ω chals pubs vals hinj _
    · rw [walkEKh_next δF b kr hn nodes ω chals pubs vals hinj hadj i hi]
      exact walkEKh_cnt δF b kr hn nodes ω chals pubs vals hinj _
    · rw [walkEKh_next δF b kr hn nodes ω chals pubs vals hinj hadj i hi]
      exact walkEKh_acc δF b kr hn nodes ω chals pubs vals hinj _
    · rw [walkEFh_next_base δF b kr hn nodes ω chals pubs vals hinj hadj i hi (show 2 ≤ WChip.rM by decide)
        (show WChip.rM < 21 by decide)]
      rfl
  intro g hg
  simp only [WChip.walkGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [MixedExpr.eval, CoeffExpr.eval, cv, WChip.isF, WChip.vC, WChip.αE, m0, tln, hch]
    by_cases h0 : (i : ℕ) = 0
    · rw [if_pos h0, hk.ln_first h0]; simp
    · rw [if_neg h0]; simp
  · simp only [MixedExpr.eval, CoeffExpr.eval, cv, notE, WChip.isL, WChip.vC, WChip.vN, WChip.αE, m1, tln, hch]
    by_cases hl : (i : ℕ) + 1 = n
    · rw [if_pos (hiff.mpr hl)]; simp
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      rw [if_neg (fun h => hl (hiff.mp h)), (hnext hi).2.2.2.1, hk.ln_step hi]; simp
  · simp only [MixedExpr.eval, CoeffExpr.eval, cv, WChip.isF, WChip.vC, WChip.αk, WChip.αE, m0, tcnt, hch,
      ccC.1]
    by_cases h0 : (i : ℕ) = 0
    · rw [if_pos h0, hk.cnt_first h0]; simp
    · rw [if_neg h0]; simp
  · simp only [MixedExpr.eval, CoeffExpr.eval, cv, notE, WChip.isL, WChip.vC, WChip.vN, m1, tcnt]
    by_cases hl : (i : ℕ) + 1 = n
    · rw [if_pos (hiff.mpr hl)]; simp
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      rw [if_neg (fun h => hl (hiff.mp h)), (hnext hi).2.2.2.2.1, (hnext hi).1, hk.cnt_step hi]; simp
  · simp only [MixedExpr.eval, CoeffExpr.eval, cv, WChip.isF, WChip.vC, WChip.αk, WChip.αE, m0, tacc, hch,
      ccC.2]
    by_cases h0 : (i : ℕ) = 0
    · rw [if_pos h0, hk.acc_first h0]; simp
    · rw [if_neg h0]; simp
  · simp only [MixedExpr.eval, CoeffExpr.eval, cv, nv, notE, WChip.isL, WChip.vC, WChip.vN, m1, tacc, tcnt]
    by_cases hl : (i : ℕ) + 1 = n
    · rw [if_pos (hiff.mpr hl)]; simp
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      obtain ⟨-, hcc, hcu, hln, -, hac, hrm⟩ := hnext hi
      rw [if_neg (fun h => hl (hiff.mp h)), hcc, hcu, hln, hac, hrm]
      have := hk.acc_step hi
      simp only [map_sub, map_one, map_zero, sub_zero, one_mul] at this ⊢
      linear_combination this
  · simp only [MixedExpr.eval, CoeffExpr.eval, cv, WChip.isL, WChip.vC, m1, tacc]
    by_cases hl : (i : ℕ) + 1 = n
    · rw [if_pos (hiff.mpr hl), hk.acc_last hl]; simp
    · rw [if_neg (fun h => hl (hiff.mp h))]; simp

end KGates

section Mixed
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) (kr : ℕ) {n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (ω : F) (chals pubs : ℕ → K)
  (vals : Fin n → WalkVals F K (Quad (algebraMap F K δF)))

/-- The consumed export key `(p, l, r, idx, 0)` of a walk row. -/
def wxKeyV (c : WalkVals F K (Quad (algebraMap F K δF))) : Fin 11 → Quad (algebraMap F K δF) :=
  ![c.p.size, c.p.dyck, c.p.leaf, c.l.size, c.l.dyck, c.l.leaf, c.r.size, c.r.dyck, c.r.leaf,
    liftQ δF c.idx, liftQ δF 0]

/-- The left path record `(root, l, 2·prefix, rootIdx)`. -/
def wrecLV (c : WalkVals F K (Quad (algebraMap F K δF))) : Fin 8 → Quad (algebraMap F K δF) :=
  ![c.root.size, c.root.dyck, c.root.leaf, c.l.size, c.l.dyck, c.l.leaf, liftQ δF (2 * c.pre),
    liftQ δF c.ridx]

/-- The right path record `(root, r, 2·prefix + 1, rootIdx)`. -/
def wrecRV (c : WalkVals F K (Quad (algebraMap F K δF))) : Fin 8 → Quad (algebraMap F K δF) :=
  ![c.root.size, c.root.dyck, c.root.leaf, c.r.size, c.r.dyck, c.r.leaf, liftQ δF (2 * c.pre + 1),
    liftQ δF c.ridx]

/-- The path-accumulator row term `mL·invL + mR·invR`. -/
def wpTermV (c : WalkVals F K (Quad (algebraMap F K δF))) : Quad (algebraMap F K δF) :=
  liftQ δF c.mL * c.pInvL + liftQ δF c.mR * c.pInvR

/-- **The semantic content of the `12` walk `𝕂′` equations at row `i`.** -/
structure WalkMixedFacts (γ ρ : Quad (algebraMap F K δF)) (i : Fin n) : Prop where
  root_eq : (i : ℕ) < kr → (vals i).root = (vals i).p
  xInv_den : (vals i).xInv * FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δF (vals i)) = 1
  pInvL_den : (vals i).pInvL * FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δF (vals i)) = 1
  pInvR_den : (vals i).pInvR * FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δF (vals i)) = 1
  xAcc_init : (i : ℕ) = 0 → (vals i).xAcc = (vals i).xInv
  xAcc_step : ∀ hi : (i : ℕ) + 1 < n,
    (vals ⟨(i : ℕ) + 1, hi⟩).xAcc = (vals i).xAcc + (vals ⟨(i : ℕ) + 1, hi⟩).xInv
  xAcc_term : (i : ℕ) + 1 = n → (vals i).xAcc = Quad.mk _ (pubs 0) (pubs 1)
  pAcc_init : (i : ℕ) = 0 → (vals i).pAcc = wpTermV δF (vals i)
  pAcc_step : ∀ hi : (i : ℕ) + 1 < n,
    (vals ⟨(i : ℕ) + 1, hi⟩).pAcc = (vals i).pAcc + wpTermV δF (vals ⟨(i : ℕ) + 1, hi⟩)
  pAcc_term : (i : ℕ) + 1 = n → (vals i).pAcc = Quad.mk _ (pubs 2) (pubs 3)

theorem walk_qroles (hinj : Function.Injective nodes) (i : Fin n) :
    let eK := walkEKh δF b kr hn nodes ω chals pubs vals i
    let eF := walkEFh δF b kr hn nodes ω chals pubs vals i
    (QE.var 0 : QE F).ev δF eK eF = (vals i).p.size ∧ (QE.var 2 : QE F).ev δF eK eF = (vals i).p.dyck ∧
    (QE.var 4 : QE F).ev δF eK eF = (vals i).p.leaf ∧ (QE.var 6 : QE F).ev δF eK eF = (vals i).l.size ∧
    (QE.var 8 : QE F).ev δF eK eF = (vals i).l.dyck ∧ (QE.var 10 : QE F).ev δF eK eF = (vals i).l.leaf ∧
    (QE.var 12 : QE F).ev δF eK eF = (vals i).r.size ∧ (QE.var 14 : QE F).ev δF eK eF = (vals i).r.dyck ∧
    (QE.var 16 : QE F).ev δF eK eF = (vals i).r.leaf ∧ (QE.var 18 : QE F).ev δF eK eF = (vals i).root.size ∧
    (QE.var 20 : QE F).ev δF eK eF = (vals i).root.dyck ∧ (QE.var 22 : QE F).ev δF eK eF = (vals i).root.leaf ∧
    (QE.var 27 : QE F).ev δF eK eF = (vals i).xInv ∧ (QE.var 29 : QE F).ev δF eK eF = (vals i).pInvL ∧
    (QE.var 31 : QE F).ev δF eK eF = (vals i).pInvR ∧ (QE.var 33 : QE F).ev δF eK eF = (vals i).xAcc ∧
    (QE.var 35 : QE F).ev δF eK eF = (vals i).pAcc := by
  intro eK eF
  have h := fun (s : ℕ) (hs : s < 12) => walkEKh_ev_fp δF b kr hn nodes ω chals pubs vals hinj i hs
  have g := fun (s : ℕ) (hs : s < 5) => walkEKh_ev_io δF b kr hn nodes ω chals pubs vals hinj i hs
  exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num),
    h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num), h 8 (by norm_num), h 9 (by norm_num),
    h 10 (by norm_num), h 11 (by norm_num), g 0 (by norm_num), g 1 (by norm_num), g 2 (by norm_num),
    g 3 (by norm_num), g 4 (by norm_num)⟩

theorem walk_qnext (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (r : ℕ) :
    (QE.next r : QE F).ev δF (walkEKh δF b kr hn nodes ω chals pubs vals i)
        (walkEFh δF b kr hn nodes ω chals pubs vals i) =
      (QE.var r : QE F).ev δF (walkEKh δF b kr hn nodes ω chals pubs vals ⟨(i : ℕ) + 1, hi⟩)
        (walkEFh δF b kr hn nodes ω chals pubs vals ⟨(i : ℕ) + 1, hi⟩) := by
  rw [ev_next, ev_var, walkEKh_next δF b kr hn nodes ω chals pubs vals hinj hadj i hi,
    walkEKh_next δF b kr hn nodes ω chals pubs vals hinj hadj i hi]

theorem walk_keyVec_x (hinj : Function.Injective nodes) (i : Fin n) :
    keyVec δF 11 WChip.xKey (walkEKh δF b kr hn nodes ω chals pubs vals i)
      (walkEFh δF b kr hn nodes ω chals pubs vals i) = wxKeyV δF (vals i) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, -⟩ := walk_qroles δF b kr hn nodes ω chals pubs vals hinj i
  have c3 : (walkEFh δF b kr hn nodes ω chals pubs vals i).trace 3 = (vals i).idx := by
    rw [walkEFh_base δF b kr hn nodes ω chals pubs vals hinj i (show 2 ≤ 3 by norm_num) (show 3 < 21 by norm_num)]; rfl
  funext c
  fin_cases c <;>
    simp [keyVec, WChip.xKey, QFP.entries, QFP.var, WChip.pR, WChip.lR, WChip.rR, wxKeyV,
      p0, p1, p2, p3, p4, p5, p6, p7, p8, ev_base, CoeffExpr.eval, cv, cst, WChip.idx, c3] <;> rfl

theorem walk_keyVec_L (hinj : Function.Injective nodes) (i : Fin n) :
    keyVec δF 8 WChip.recL (walkEKh δF b kr hn nodes ω chals pubs vals i)
      (walkEFh δF b kr hn nodes ω chals pubs vals i) = wrecLV δF (vals i) := by
  obtain ⟨-, -, -, p3, p4, p5, -, -, -, p9, p10, p11, -⟩ :=
    walk_qroles δF b kr hn nodes ω chals pubs vals hinj i
  have c4 : (walkEFh δF b kr hn nodes ω chals pubs vals i).trace 4 = (vals i).pre := by
    rw [walkEFh_base δF b kr hn nodes ω chals pubs vals hinj i (show 2 ≤ 4 by norm_num) (show 4 < 21 by norm_num)]; rfl
  have c5 : (walkEFh δF b kr hn nodes ω chals pubs vals i).trace 5 = (vals i).ridx := by
    rw [walkEFh_base δF b kr hn nodes ω chals pubs vals hinj i (show 2 ≤ 5 by norm_num) (show 5 < 21 by norm_num)]; rfl
  funext c
  fin_cases c <;>
    simp [keyVec, WChip.recL, QFP.entries, QFP.var, WChip.rootR, WChip.lR, wrecLV,
      p3, p4, p5, p9, p10, p11, ev_base, CoeffExpr.eval, cv, cst, WChip.pre, WChip.ridx, c4, c5] <;> rfl

theorem walk_keyVec_R (hinj : Function.Injective nodes) (i : Fin n) :
    keyVec δF 8 WChip.recR (walkEKh δF b kr hn nodes ω chals pubs vals i)
      (walkEFh δF b kr hn nodes ω chals pubs vals i) = wrecRV δF (vals i) := by
  obtain ⟨-, -, -, -, -, -, p6, p7, p8, p9, p10, p11, -⟩ :=
    walk_qroles δF b kr hn nodes ω chals pubs vals hinj i
  have c4 : (walkEFh δF b kr hn nodes ω chals pubs vals i).trace 4 = (vals i).pre := by
    rw [walkEFh_base δF b kr hn nodes ω chals pubs vals hinj i (show 2 ≤ 4 by norm_num) (show 4 < 21 by norm_num)]; rfl
  have c5 : (walkEFh δF b kr hn nodes ω chals pubs vals i).trace 5 = (vals i).ridx := by
    rw [walkEFh_base δF b kr hn nodes ω chals pubs vals hinj i (show 2 ≤ 5 by norm_num) (show 5 < 21 by norm_num)]; rfl
  funext c
  fin_cases c <;>
    simp [keyVec, WChip.recR, QFP.entries, QFP.var, WChip.rootR, WChip.rR, wrecRV,
      p6, p7, p8, p9, p10, p11, ev_base, CoeffExpr.eval, cv, cst, WChip.pre, WChip.ridx, c4, c5] <;> rfl

variable [DecidableEq F] in
/-- **The `12` walk `𝕂′` equations hold at the honest environment of row `i`.** -/
theorem walk_qEqs_hold (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11)
    (hf : WalkMixedFacts δF kr pubs vals γ ρ i) :
    ∀ e ∈ WChip.qEqs δF, e.ev δF (walkEKh δF b kr hn nodes ω chals pubs vals i)
      (walkEFh δF b kr hn nodes ω chals pubs vals i) = 0 := by
  obtain ⟨p0, p2, p4, p6, p8, p10, p12, p14, p16, p18, p20, p22, p27, p29, p31, p33, p35⟩ :=
    walk_qroles δF b kr hn nodes ω chals pubs vals hinj i
  set eK := walkEKh δF b kr hn nodes ω chals pubs vals i with heK
  set eF := walkEFh δF b kr hn nodes ω chals pubs vals i with heF
  have m0 : eF.trace 0 = if (i : ℕ) = 0 then 1 else 0 :=
    walkEFh_mask0 δF b kr hn nodes ω chals pubs vals hinj i
  have m1 : eF.trace 1 = if i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩ then 1 else 0 :=
    walkEFh_mask1 δF b kr hn nodes ω chals pubs vals hinj i
  have m2 : eF.trace 2 = if (i : ℕ) < kr then 1 else 0 := by
    rw [heF, walkEFh_base δF b kr hn nodes ω chals pubs vals hinj i le_rfl (by norm_num)]; rfl
  have hch : ChalsOK δF eK.chal γ ρ 11 := by rw [heK, walkEKh_chal]; exact hok
  have dX : (den δF WChip.xKey).ev δF eK eF = FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δF (vals i)) := by
    rw [den_ev_compress' δF WChip.xKey (m := 11) rfl _ _ γ ρ hch,
      walk_keyVec_x δF b kr hn nodes ω chals pubs vals hinj i]
  have dL : (den δF WChip.recL).ev δF eK eF = FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δF (vals i)) := by
    rw [den_ev_compress' δF WChip.recL (m := 8) rfl _ _ γ ρ (chalsOK_mono δF (by norm_num) hch),
      walk_keyVec_L δF b kr hn nodes ω chals pubs vals hinj i]
  have dR : (den δF WChip.recR).ev δF eK eF = FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δF (vals i)) := by
    rw [den_ev_compress' δF WChip.recR (m := 8) rfl _ _ γ ρ (chalsOK_mono δF (by norm_num) hch),
      walk_keyVec_R δF b kr hn nodes ω chals pubs vals hinj i]
  have hiff := walk_hiff hn i
  have hnotE : ∀ j, (notE (cv j) : CoeffExpr F).eval eF = 1 - eF.trace j := fun j => rfl
  have hpub0 : (QE.pub 0 : QE F).ev δF eK eF = Quad.mk _ (pubs 0) (pubs 1) := by
    rw [ev_pub, walkEKh_pub, walkEKh_pub]
  have hpub2 : (QE.pub 2 : QE F).ev δF eK eF = Quad.mk _ (pubs 2) (pubs 3) := by
    rw [ev_pub, walkEKh_pub, walkEKh_pub]
  have hm : ∀ j, 2 ≤ j → j < 21 → eF.trace j = (vals i).base kr i j := fun j h2 hj =>
    walkEFh_base δF b kr hn nodes ω chals pubs vals hinj i h2 hj
  have tmL : eF.trace WChip.mL = (vals i).mL := by rw [show WChip.mL = 10 from rfl, hm 10 (by norm_num) (by norm_num)]; rfl
  have tmR : eF.trace WChip.mR = (vals i).mR := by rw [show WChip.mR = 11 from rfl, hm 11 (by norm_num) (by norm_num)]; rfl
  have hroot : ∀ (P : Quad (algebraMap F K δF)) (hP : (i : ℕ) < kr → P = 0),
      liftQ δF (if (i : ℕ) < kr then 1 else 0) * P = 0 := by
    intro P hP
    by_cases hk : (i : ℕ) < kr
    · rw [hP hk]; simp
    · rw [if_neg hk]; simp [liftQ]
  intro e he
  simp only [WChip.qEqs, QFP.entries, QFP.scale, QFP.sub, QFP.var, WChip.rootR, WChip.pR,
    Nat.reduceAdd, zero_add, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [ev_scale, ev_sub, CoeffExpr.eval, cv, WChip.rM, m2, p18, p0]
    exact hroot _ fun hk => by rw [hf.root_eq hk]; simp
  · simp only [ev_scale, ev_sub, CoeffExpr.eval, cv, WChip.rM, m2, p20, p2]
    exact hroot _ fun hk => by rw [hf.root_eq hk]; simp
  · simp only [ev_scale, ev_sub, CoeffExpr.eval, cv, WChip.rM, m2, p22, p4]
    exact hroot _ fun hk => by rw [hf.root_eq hk]; simp
  · simp only [ev_sub, ev_mul, ev_one, WChip.xInv, p27, dX]
    exact sub_eq_zero.mpr hf.xInv_den
  · simp only [ev_sub, ev_mul, ev_one, WChip.pInvL, p29, dL]
    exact sub_eq_zero.mpr hf.pInvL_den
  · simp only [ev_sub, ev_mul, ev_one, WChip.pInvR, p31, dR]
    exact sub_eq_zero.mpr hf.pInvR_den
  · -- xAcc init
    simp only [ev_scale, ev_sub, CoeffExpr.eval, cv, WChip.isF, WChip.xAcc, WChip.xInv, p33, p27, m0]
    by_cases h0 : (i : ℕ) = 0
    · rw [if_pos h0]; simp [liftQ, hf.xAcc_init h0]
    · rw [if_neg h0]; simp [liftQ]
  · -- xAcc step
    by_cases hl : (i : ℕ) + 1 = n
    · simp only [ev_scale, hnotE, WChip.isL, m1, if_pos (hiff.mpr hl)]; simp [liftQ]
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      have q := walk_qnext δF b kr hn nodes ω chals pubs vals hinj hadj i hi
      rw [← heK, ← heF] at q
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, n27, -, -, n33, -⟩ :=
        walk_qroles δF b kr hn nodes ω chals pubs vals hinj ⟨(i : ℕ) + 1, hi⟩
      simp only [ev_scale, ev_sub, hnotE, WChip.isL, m1, if_neg (fun h => hl (hiff.mp h)), WChip.xAcc,
        WChip.xInv, q, n27, n33, p33]
      have := hf.xAcc_step hi
      simp only [liftQ, sub_zero, map_one, one_mul]
      linear_combination this
  · -- xAcc terminal
    by_cases hl : (i : ℕ) + 1 = n
    · simp only [ev_scale, ev_sub, hpub0, CoeffExpr.eval, cv, WChip.isL, m1, if_pos (hiff.mpr hl),
        WChip.xAcc, p33]
      simp [liftQ, hf.xAcc_term hl]
    · simp only [ev_scale, CoeffExpr.eval, cv, WChip.isL, m1, if_neg (fun h => hl (hiff.mp h))]; simp [liftQ]
  · -- pAcc init
    simp only [ev_scale, ev_sub, ev_add, CoeffExpr.eval, cv, WChip.isF, WChip.pAcc, WChip.pInvL, WChip.pInvR,
      WChip.pTerm, if_true, p35, p29, p31, m0, tmL, tmR]
    by_cases h0 : (i : ℕ) = 0
    · rw [if_pos h0]; simp [liftQ, hf.pAcc_init h0, wpTermV]
    · rw [if_neg h0]; simp [liftQ]
  · -- pAcc step
    by_cases hl : (i : ℕ) + 1 = n
    · simp only [ev_scale, hnotE, WChip.isL, m1, if_pos (hiff.mpr hl)]; simp [liftQ]
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      have q := walk_qnext δF b kr hn nodes ω chals pubs vals hinj hadj i hi
      rw [← heK, ← heF] at q
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, n29, n31, -, n35⟩ :=
        walk_qroles δF b kr hn nodes ω chals pubs vals hinj ⟨(i : ℕ) + 1, hi⟩
      have nL : eF.traceNext WChip.mL = (vals ⟨(i : ℕ) + 1, hi⟩).mL := by
        rw [heF, show WChip.mL = 10 from rfl, walkEFh_next_base δF b kr hn nodes ω chals pubs vals hinj hadj i hi (show 2 ≤ 10 by norm_num)
          (show 10 < 21 by norm_num)]; rfl
      have nR : eF.traceNext WChip.mR = (vals ⟨(i : ℕ) + 1, hi⟩).mR := by
        rw [heF, show WChip.mR = 11 from rfl, walkEFh_next_base δF b kr hn nodes ω chals pubs vals hinj hadj i hi (show 2 ≤ 11 by norm_num)
          (show 11 < 21 by norm_num)]; rfl
      simp only [ev_scale, ev_sub, ev_add, hnotE, WChip.isL, m1, if_neg (fun h => hl (hiff.mp h)), WChip.pAcc,
        WChip.pInvL, WChip.pInvR, WChip.pTerm, Bool.false_eq_true, if_false, CoeffExpr.eval, nv, q, n29, n31,
        n35, p35, nL, nR]
      have := hf.pAcc_step hi
      simp only [wpTermV] at this
      simp only [liftQ, sub_zero, map_one, one_mul]
      linear_combination this
  · -- pAcc terminal
    by_cases hl : (i : ℕ) + 1 = n
    · simp only [ev_scale, ev_sub, hpub2, CoeffExpr.eval, cv, WChip.isL, m1, if_pos (hiff.mpr hl),
        WChip.pAcc, p35]
      simp [liftQ, hf.pAcc_term hl]
    · simp only [ev_scale, CoeffExpr.eval, cv, WChip.isL, m1, if_neg (fun h => hl (hiff.mp h))]; simp [liftQ]

end Mixed

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
