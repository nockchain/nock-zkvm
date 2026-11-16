/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/WalkBridgeX9.lean

* `rowW9` — the walk decoding: `rowOfX9`, except that an `old s10L` row is read by its committed chip child label
    (shaped as an `s3` row).  `kidsX9_rowW9_of_halving`: exact halving gives the real row's kid.
  * `childrenX9_eval`, `ccLX9_eval`, `cmLX9_eval`, ... : the walk gate's `𝕂` terms evaluate to `rlc γ (encT …)` of the
    decoded handles (the new states' third / second kid reads the routed label column `lab = (kLabX, vLabX)`).
  * `WalkRowsX9` / `cwalkX9_sat`, `walkRowsX9_of_sat` / `cwalkX9_of_sat`, `goalJ9A`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.WalkTreeX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.RapWalkX9
import Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeX9

open Nock Nock.Reified Nock.Framework Nock.Edit Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd chalAlphaW chalGammaW pubIC pubSeed pubOut cc notC kv wv)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (HalvingOK)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 (csIdx rowOfX9)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeX9
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9
open Module
open scoped Polynomial

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-! ## 1. The walk decoding -/

/-- **The walk decoding of a twin row**: `rowOfX9`, with an `old s10L` row read through its chip child label. -/
def rowW9 (env : Env (ZMod p)) : CSt → RowVSX9
  | .old .s10L =>
    ⟨.old .s3, { rowOfX env .s10L with st := .s3, ft := (0, (env.trace vX).val), sf1 := hdV env xE },
      hdV env ⟨kLabX, vLabX⟩⟩
  | cs => rowOfX9 env cs

theorem rowW9_trip (env : Env (ZMod p)) (cs : CSt) : (rowW9 env cs).trip = (rowOfX9 env cs).trip := by
  cases cs with
  | old st => cases st <;> rfl
  | s0B => rfl
  | s10B => rfl
  | s10S => rfl

theorem fanS9_rowW9 (env : Env (ZMod p)) (cs : CSt) : fanS9 (rowW9 env cs).cs = fanS9 cs := by
  cases cs with
  | old st => cases st <;> rfl
  | s0B => rfl
  | s10B => rfl
  | s10S => rfl

theorem wf9_rowW9 (env : Env (ZMod p)) (cs : CSt) : WF9 (rowW9 env cs) := by
  intro st h
  cases cs with
  | old st0 => cases st0 <;> (cases h; rfl)
  | s0B => cases h
  | s10B => cases h
  | s10S => cases h

theorem rowW9_of_ne (env : Env (ZMod p)) {cs : CSt} (h : cs ≠ .old .s10L) : rowW9 env cs = rowOfX9 env cs := by
  cases cs with
  | old st => cases st <;> first | rfl | exact absurd rfl h
  | s0B => rfl
  | s10B => rfl
  | s10S => rfl

theorem kidsX9_rowW9_s10L (env : Env (ZMod p)) :
    kidsX9 (rowW9 env (.old .s10L)) = [(hdV env xS, (0, (env.trace vX).val), hdV env xE)] := rfl

/-- **Exact halving ⇒ the chip kid is the `kidsX9` kid** (`f.v = 2 v + β`, no wrap), at the twin's one-hot. -/
theorem kidsX9_rowW9_of_halving {env : Env (ZMod p)} (hB : BaseHoldsX9 env) (hOH : OneHotAt9 env 12)
    (hv : HalvingOK env .s10L) : kidsX9 (rowW9 env (.old .s10L)) = kidsX9 (rowOfX9 env (.old .s10L)) := by
  have hN := hOH.newOff (show 12 < nStates by decide)
  have hB8 := baseHoldsX_of_X9 hB hN
  have hOH8 : OneHotAt env 12 := fun i hi => hOH i (List.mem_append_left _ (List.mem_range.mpr hi))
  have e1 : kidsX9 (rowW9 env (.old .s10L)) = kidsX (WalkBridgeJ8.rowW env .s10L) := rfl
  have e2 : kidsX9 (rowOfX9 env (.old .s10L)) = kidsX (rowOfX env .s10L) := rfl
  rw [e1, e2]
  exact WalkBridgeJ8.kidsX_rowW_of_halving hB8 hOH8 hv

theorem rowW9_base (env : Env (ZMod p)) (cs : CSt) :
    (rowW9 env cs).base = WalkBridgeJ8.rowW env (match cs with | .old st => st | _ => .s0) := by
  cases cs with
  | old st => cases st <;> rfl
  | s0B => rfl
  | s10B => rfl
  | s10S => rfl

/-- Every decoded handle value (and the routed label) is below `p`. -/
theorem smallR9_rowW9 (env : Env (ZMod p)) (cs : CSt) : SmallR9 p (rowW9 env cs) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [rowW9_base]; exact WalkBridgeJ8.smallR_rowW _ _
  · cases cs with
    | old st => cases st <;> exact ZMod.val_lt _
    | s0B => exact ZMod.val_lt _
    | s10B => exact ZMod.val_lt _
    | s10S => exact ZMod.val_lt _
  · cases cs with
    | old st => cases st <;> exact ZMod.val_lt _
    | s0B => exact ZMod.val_lt _
    | s10B => exact ZMod.val_lt _
    | s10S => exact ZMod.val_lt _

theorem childrenX9_len (cs : CSt) : (childrenX9 (csIdx cs)).length = fanS9 cs := by
  cases cs with
  | old st => cases st <;> rfl
  | s0B => rfl
  | s10B => rfl
  | s10S => rfl

theorem list_sum_ite {K : Type} [Field K] (X : ℕ → K) :
    ∀ (l : List ℕ) (a : ℕ), l.Nodup → a ∈ l → (l.map fun j => if j = a then X j else 0).sum = X a
  | [], a, _, h => by simp at h
  | b :: l, a, hnd, ha => by
    rw [List.nodup_cons] at hnd
    by_cases hba : b = a
    · subst hba
      have : (l.map fun j => if j = b then X j else 0) = l.map (fun _ => 0) :=
        List.map_congr_left fun j hj => by rw [if_neg (fun h => hnd.1 (by rw [← h]; exact hj))]
      rw [List.map_cons, List.sum_cons, if_pos rfl, this]
      simp
    · have ha' : a ∈ l := (List.mem_cons.mp ha).resolve_left (fun h => hba h.symm)
      rw [List.map_cons, List.sum_cons, if_neg hba, zero_add]
      exact list_sum_ite X l a hnd.2 ha'

theorem statesX9_nodup : statesX9.Nodup := by decide +kernel

theorem csIdx_mem (cs : CSt) : csIdx cs ∈ statesX9 := by
  cases cs with
  | old st =>
    exact List.mem_append_left _ (List.mem_range.mpr (by cases st <;> decide))
  | s0B => simp [csIdx, statesX9, newStates, sS0B]
  | s10B => simp [csIdx, statesX9, newStates, sS10B]
  | s10S => simp [csIdx, statesX9, newStates, sS10S]

/-! ## 2. The walk gate's `𝕂` terms -/

section Eval
variable {K : Type} [Field K] [Algebra (ZMod p) K]

variable (eK : Env K) (eF : Env (ZMod p)) (kind : VarKind) (e' : Env (ZMod p))
  (hk : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF = e'.trace i)
include hk

theorem curLX_eval9 (cs : CSt) :
    evalMQ (curLX kind : MixedExpr ℚ) eK eF =
      Walk.rlc (eK.chal chalGammaW) (encT (K := K) (rowW9 e' cs).trip) := by
  rw [rowW9_trip]
  exact WalkBridgeJ8.lab_eval eK eF kind e' hk _ _ _ _

theorem childrenX9_eval (γ : ℕ) (cs : CSt) (i : ℕ) (hi : i < fanS9 cs) :
    evalMQ (rlcKeyL kind γ 0 ((childrenX9 (csIdx cs)).getD i []) : MixedExpr ℚ) eK eF =
      Walk.rlc (eK.chal γ) (encT (K := K) ((kidsX9 (rowW9 e' cs)).getD i trip0)) := by
  have l := WalkBridgeJ8.lab_eval eK eF kind e' hk γ
  cases cs with
  | old st =>
    have e1 : childrenX9 (csIdx (.old st)) = childrenX (stIdx st) := by cases st <;> rfl
    have e2 : kidsX9 (rowW9 e' (.old st)) = kidsX (WalkBridgeJ8.rowW e' st) := by cases st <;> rfl
    rw [e1, e2]
    exact WalkBridgeJ8.childrenX_eval eK eF kind e' hk γ st i hi
  | s0B => simp [fanS9] at hi
  | s10B =>
    simp only [fanS9] at hi
    interval_cases i
    · exact l xS xFttt xSf1
    · exact l xS xFtt xSf2
    · exact l xSf2 ⟨kLabX, vLabX⟩ xE
  | s10S =>
    simp only [fanS9] at hi
    interval_cases i
    · exact l xS xM xE
    · exact l xFtth ⟨kLabX, vLabX⟩ xFttt

omit hk in
theorem sum_onehotX9 (X : ℕ → K) (cs : CSt) (hOH : OneHotAt9 e' (csIdx cs)) :
    (statesX9.map fun j => algebraMap (ZMod p) K (e'.trace j) * X j).sum = X (csIdx cs) := by
  have : statesX9.map (fun j => algebraMap (ZMod p) K (e'.trace j) * X j) =
      statesX9.map (fun j => if j = csIdx cs then X j else 0) :=
    List.map_congr_left fun j hj => by
      rw [hOH j hj]; split_ifs <;> simp
  rw [this]
  exact list_sum_ite X _ _ statesX9_nodup (csIdx_mem cs)

theorem ccLX9_eval (cs : CSt) (hOH : OneHotAt9 e' (csIdx cs)) :
    evalMQ (ccLX9 kind : MixedExpr ℚ) eK eF =
      ∑ i ∈ Finset.range (fanS9 cs), eK.chal chalAlphaW ^ (i + 1) *
        Walk.rlc (eK.chal chalGammaW) (encT (K := K) ((kidsX9 (rowW9 e' cs)).getD i trip0)) := by
  unfold ccLX9
  rw [WalkBridgeJ8.evalMQ_sumM' eK eF, List.map_map]
  have h1 : ∀ j, evalMQ (MixedExpr.Scale (kv kind j) (childSumX9 kind j) : MixedExpr ℚ) eK eF =
      algebraMap (ZMod p) K (e'.trace j) * evalMQ (childSumX9 kind j : MixedExpr ℚ) eK eF := by
    intro j; simp only [evalMQ, kv, hk]
  simp only [Function.comp_def, h1]
  rw [sum_onehotX9 (e' := e') (fun j => evalMQ (childSumX9 kind j : MixedExpr ℚ) eK eF) cs hOH]
  unfold childSumX9
  rw [WalkBridgeJ8.evalMQ_sumM' eK eF, List.map_map]
  have h2 : ∀ q : List (Option ℕ) × ℕ, evalMQ (MixedExpr.Mul (MixedExpr.Pow
      (MixedExpr.Var .challenge chalAlphaW) (q.2 + 1)) (rlcKeyL kind chalGammaW 0 q.1) : MixedExpr ℚ) eK eF =
      eK.chal chalAlphaW ^ (q.2 + 1) * evalMQ (rlcKeyL kind chalGammaW 0 q.1 : MixedExpr ℚ) eK eF := by
    intro q; simp only [evalMQ]
  simp only [Function.comp_def, h2]
  rw [WalkBridgeJ8.zipIdx_sum' [] (fun q1 q2 => eK.chal chalAlphaW ^ (q2 + 1) *
    evalMQ (rlcKeyL kind chalGammaW 0 q1 : MixedExpr ℚ) eK eF) (childrenX9 (csIdx cs)) 0, childrenX9_len]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [childrenX9_eval eK eF kind e' hk chalGammaW cs i (Finset.mem_range.mp hi), zero_add]

theorem cmLX9_eval (cs : CSt) (hOH : OneHotAt9 e' (csIdx cs)) :
    evalMQ (cmLX9 kind : MixedExpr ℚ) eK eF = eK.chal chalAlphaW ^ (fanS9 cs) := by
  unfold cmLX9
  rw [WalkBridgeJ8.evalMQ_sumM' eK eF, List.map_map]
  have h1 : ∀ j, evalMQ (MixedExpr.Scale (kv kind j) (MixedExpr.Pow (MixedExpr.Var .challenge chalAlphaW)
      (childrenX9 j).length) : MixedExpr ℚ) eK eF =
      algebraMap (ZMod p) K (e'.trace j) * eK.chal chalAlphaW ^ (childrenX9 j).length := by
    intro j; simp only [evalMQ, kv, hk]
  simp only [Function.comp_def, h1]
  rw [sum_onehotX9 (e' := e') (fun j => eK.chal chalAlphaW ^ (childrenX9 j).length) cs hOH, childrenX9_len]

end Eval

/-! ## 3. The compute walk over an accepted row sequence -/

section Seq
variable {K : Type} [Field K] [Algebra (ZMod p) K]

/-- **An accepted twin compute-walk row sequence** (`WalkRowsX` at 20 states, `walkGatesX9`). -/
structure WalkRowsX9 (n : ℕ) (E : ℕ → Env (ZMod p)) (EK : ℕ → Env K) (st : ℕ → CSt)
    (α γ seed : K) : Prop where
  hn : 0 < n
  oh : ∀ r < n, OneHotAt9 (E r) (csIdx (st r))
  gate : ∀ r < n, ∀ g ∈ (walkGatesX9 : List (MixedExpr ℚ)), evalMQ g (EK r) (E r) = 0
  next : ∀ r, r + 1 < n → (E r).traceNext = (E (r + 1)).trace
  nextK : ∀ r, r + 1 < n → (EK r).traceNext = (EK (r + 1)).trace
  first : ∀ r < n, (E r).trace firstX = if r = 0 then 1 else 0
  last : ∀ r < n, (E r).trace lastX = if r = n - 1 then 1 else 0
  chA : ∀ r, (EK r).chal chalAlphaW = α
  chG : ∀ r, (EK r).chal chalGammaW = γ
  pIC : ∀ r, (EK r).pub pubIC = α
  pSeed : ∀ r, (EK r).pub pubSeed = seed
  pOut : ∀ r, (EK r).pub pubOut = 0

/-- The walk-decoded rows, 1-indexed. -/
def rowsWX9 (E : ℕ → Env (ZMod p)) (st : ℕ → CSt) (i : ℕ) : RowVSX9 := rowW9 (E (i - 1)) (st (i - 1))

variable {n : ℕ} {E : ℕ → Env (ZMod p)} {EK : ℕ → Env K} {st : ℕ → CSt} {α γ seed : K}
  (C : WalkRowsX9 n E EK st α γ seed)
include C

theorem lastZ {r : ℕ} (hr : r + 1 < n) : (E r).trace lastX = 0 := by
  rw [C.last r (by omega)]; simp; omega

theorem hkN {r : ℕ} (hr : r + 1 < n) :
    ∀ i, evalQ (.var .traceNext i : CoeffExpr ℚ) (E r) = (E (r + 1)).trace i := fun i => by
  show (E r).traceNext i = _
  rw [C.next r hr]

theorem gX {r : ℕ} (hr : r < n) (k : ℕ) (hk : k < 9) :
    evalMQ ((walkGatesX9 : List (MixedExpr ℚ))[k]'(by simp [walkGatesX9]; omega)) (EK r) (E r) = 0 :=
  C.gate r hr _ (List.getElem_mem _)

theorem w_ln_step {r : ℕ} (hr : r + 1 < n) :
    (EK (r + 1)).trace wLnX = α * (EK r).trace wLnX := by
  have h0 := gX C (by omega : r < n) 0 (by norm_num)
  simp [walkGatesX9, evalMQ, evalQ, notC, cc, ChipH.wv, lastZ C hr, C.nextK r hr, C.chA r,
    sub_eq_zero] at h0
  exact h0

theorem w_cnt_step {r : ℕ} (hr : r + 1 < n) :
    (EK (r + 1)).trace wCntX = (EK r).trace wCntX * α ^ (fanS9 (st (r + 1))) := by
  have h0 := gX C (by omega : r < n) 1 (by norm_num)
  have hc := cmLX9_eval (EK r) (E r) .traceNext (E (r + 1)) (hkN C hr) (st (r + 1)) (C.oh _ hr)
  simp only [walkGatesX9, List.getElem_cons_succ, List.getElem_cons_zero, evalMQ, ChipH.wv, hc] at h0
  simp [evalQ, notC, cc, lastZ C hr, C.nextK r hr, C.chA r, sub_eq_zero] at h0
  exact h0

theorem w_acc_step {r : ℕ} (hr : r + 1 < n) :
    (EK (r + 1)).trace wLnX * Walk.rlc γ (encT (K := K) (rowW9 (E (r + 1)) (st (r + 1))).trip) +
      (EK (r + 1)).trace wAccX - (EK r).trace wAccX =
    ∑ i ∈ Finset.range (fanS9 (st (r + 1))), (EK r).trace wCntX *
      (α ^ (i + 1) * Walk.rlc γ (encT (K := K) ((kidsX9 (rowW9 (E (r + 1)) (st (r + 1)))).getD i trip0))) := by
  have h0 := gX C (by omega : r < n) 2 (by norm_num)
  have hc := ccLX9_eval (EK r) (E r) .traceNext (E (r + 1)) (hkN C hr) (st (r + 1)) (C.oh _ hr)
  have hl := curLX_eval9 (EK r) (E r) .traceNext (E (r + 1)) (hkN C hr) (st (r + 1))
  rw [C.chA r, C.chG r] at hc
  rw [C.chG r] at hl
  simp only [walkGatesX9, List.getElem_cons_succ, List.getElem_cons_zero, evalMQ, ChipH.wv, hc, hl] at h0
  simp [evalQ, notC, cc, lastZ C hr, C.nextK r hr] at h0
  rw [← Finset.mul_sum]
  exact sub_eq_zero.mp h0

theorem first0 : (E 0).trace firstX = 1 := by rw [C.first 0 C.hn]; simp

theorem w_ln_zero : (EK 0).trace wLnX = α := by
  have h0 := gX C C.hn 3 (by norm_num)
  simp [walkGatesX9, evalMQ, evalQ, cc, ChipH.wv, first0 C, C.chA 0, sub_eq_zero] at h0
  exact h0

theorem w_cnt_zero : (EK 0).trace wCntX = α * α ^ (fanS9 (st 0)) := by
  have h0 := gX C C.hn 4 (by norm_num)
  have hc := cmLX9_eval (EK 0) (E 0) .traceCur (E 0) (fun _ => rfl) (st 0) (C.oh 0 C.hn)
  rw [C.chA 0] at hc
  simp only [walkGatesX9, List.getElem_cons_succ, List.getElem_cons_zero, evalMQ, ChipH.wv, hc] at h0
  simp [evalQ, cc, first0 C, C.pIC 0, sub_eq_zero] at h0
  exact h0

theorem w_acc_zero :
    (EK 0).trace wLnX * Walk.rlc γ (encT (K := K) (rowW9 (E 0) (st 0)).trip) + (EK 0).trace wAccX =
    α * ∑ i ∈ Finset.range (fanS9 (st 0)),
      (α ^ (i + 1) * Walk.rlc γ (encT (K := K) ((kidsX9 (rowW9 (E 0) (st 0))).getD i trip0))) + seed := by
  have h0 := gX C C.hn 5 (by norm_num)
  have hc := ccLX9_eval (EK 0) (E 0) .traceCur (E 0) (fun _ => rfl) (st 0) (C.oh 0 C.hn)
  have hl := curLX_eval9 (EK 0) (E 0) .traceCur (E 0) (fun _ => rfl) (st 0)
  rw [C.chA 0, C.chG 0] at hc
  rw [C.chG 0] at hl
  simp only [walkGatesX9, List.getElem_cons_succ, List.getElem_cons_zero, evalMQ, ChipH.wv, hc, hl] at h0
  simp [evalQ, cc, first0 C, C.pIC 0, C.pSeed 0] at h0
  exact sub_eq_zero.mp h0

theorem w_wit {r : ℕ} (hr : r + 1 < n) : (EK r).trace wCntX ≠ (EK r).trace wLnX := by
  have h0 := gX C (by omega : r < n) 6 (by norm_num)
  simp [walkGatesX9, evalMQ, evalQ, notC, cc, ChipH.wv, lastZ C hr, sub_eq_zero] at h0
  intro he
  rw [he, sub_self, mul_zero] at h0
  exact zero_ne_one h0

theorem w_last : (EK (n - 1)).trace wCntX = (EK (n - 1)).trace wLnX ∧ (EK (n - 1)).trace wAccX = 0 := by
  have hr : n - 1 < n := by have := C.hn; omega
  have m : (E (n - 1)).trace lastX = 1 := by rw [C.last _ hr]; simp
  have h7 := gX C hr 7 (by norm_num)
  have h8 := gX C hr 8 (by norm_num)
  simp [walkGatesX9, evalMQ, evalQ, cc, ChipH.wv, m, sub_eq_zero, C.pOut] at h7 h8
  exact ⟨h7, h8⟩

omit C in
theorem sum_Icc_range' {M : Type} [AddCommMonoid M] (f : ℕ → M) :
    ∀ m : ℕ, ∑ l ∈ Finset.Icc 1 m, f l = ∑ i ∈ Finset.range m, f (i + 1)
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, sum_Icc_range' f m]

omit C in
theorem foOf9_rowsWX9 (i : ℕ) : foOf9 (rowsWX9 E st) i = fanS9 (st (i - 1)) := by
  simp [foOf9, rowsWX9, fanS9_rowW9]

/-- **The compute walk of `computeChipVCLHX9`, chip → label bridge** (twin of `cwalkX_sat`). -/
theorem cwalkX9_sat
    (hseed : seed = Walk.rlc γ (encT (K := K) (rowW9 (E 0) (st 0)).trip) * α) :
    ∃ ln cnt acc : ℕ → K,
      Walk.WalkSat (fun i => Walk.rlc γ (enc9 (lblOf9 (rowsWX9 E st) i)))
        (fun i l => Walk.rlc γ (enc9 (clabOf9 (rowsWX9 E st) i l)))
        (foOf9 (rowsWX9 E st)) ln cnt acc α
        (∑ i ∈ Finset.Icc 1 1, Walk.rlc γ (enc9 (lblOf9 (rowsWX9 E st) i)) * α ^ i)
        (α ^ 1) n ∧
      acc n = 0 ∧ (∀ i, 1 ≤ i → i < n → cnt i ≠ ln i) ∧ cnt n = ln n := by
  have encL : ∀ i, enc9 (K := K) (lblOf9 (rowsWX9 E st) i) = encT (rowW9 (E (i - 1)) (st (i - 1))).trip :=
    fun _ => rfl
  have encC : ∀ i l, enc9 (K := K) (clabOf9 (rowsWX9 E st) i l) =
      encT ((kidsX9 (rowW9 (E (i - 1)) (st (i - 1)))).getD (l - 1) trip0) := by
    intro i l; simp [enc9, clabOf9, rowsWX9]
  refine ⟨fun i => (EK (i - 1)).trace wLnX, fun i => (EK (i - 1)).trace wCntX,
    fun i => (EK (i - 1)).trace wAccX, ?_, ?_, ?_, ?_⟩
  · refine
      { hpos := C.hn
        ln1 := w_ln_zero C
        lnInc := fun i hi hin => ?_
        count1 := ?_
        countInc := fun i hi hin => ?_
        accInit := ?_
        accStep := fun i hi hin => ?_ }
    · obtain ⟨r, rfl⟩ : ∃ r, i = r + 1 := ⟨i - 1, by omega⟩
      exact w_ln_step C (r := r) (by omega)
    · rw [pow_one, foOf9_rowsWX9]; exact w_cnt_zero C
    · obtain ⟨r, rfl⟩ : ∃ r, i = r + 1 := ⟨i - 1, by omega⟩
      simp only [foOf9_rowsWX9, Nat.add_sub_cancel]
      exact w_cnt_step C (r := r) (by omega)
    · have h0 := w_acc_zero C
      simp only [Finset.Icc_self, Finset.sum_singleton]
      rw [sum_Icc_range', foOf9_rowsWX9]
      simp only [pow_one, encL, encC, Nat.reduceSub, Nat.sub_self]
      rw [← hseed, h0, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Nat.add_sub_cancel]
      ring
    · obtain ⟨r, rfl⟩ : ∃ r, i = r + 1 := ⟨i - 1, by omega⟩
      have h0 := w_acc_step C (r := r) (by omega)
      rw [sum_Icc_range', foOf9_rowsWX9]
      simp only [encL, encC, Nat.add_sub_cancel]
      rw [h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
  · have := (w_last C).2
    simpa using this
  · intro i hi hin
    obtain ⟨r, rfl⟩ : ∃ r, i = r + 1 := ⟨i - 1, by omega⟩
    exact w_wit C (r := r) (by omega)
  · have := (w_last C).1
    simpa using this

end Seq

/-! ## 4. An accepted `computeChipVCLHX9` trace -/

section Chip
variable [DecidableEq (ZMod p)] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  {chalV pubVal : ℕ → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
  {P : Fin (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X]} {α γ seed : K}

local notation "EN9" => CompReqsX9.envsN9 hn nodes orbit chalV pubVal P

/-- **An accepted `computeChipVCLHX9` trace is a `WalkRowsX9`.** -/
theorem walkRowsX9_of_sat (C : XCtx hn nodes b δ chalV pubVal orbit P α γ seed) :
    WalkRowsX9 n (fun r => EN9 r) (fun r => Compute.TowerD.gatherEnv b (EN9 r))
      (fun r => stX9 (EN9 r)) α γ seed where
  hn := hn
  oh := fun r hr => ohE9 C hr
  gate := fun r hr g hg => by
    show evalMQ g (Compute.TowerD.gatherEnv b (EN9 r)) (EN9 r) = 0
    exact walkE9 C hr g hg
  next := fun r hr => tnE9 C hr
  nextK := fun r hr => by
    show Compute.LogUp.limbVal b (EN9 r).traceNext = Compute.LogUp.limbVal b (EN9 (r + 1)).trace
    rw [tnE9 C hr]
  first := fun r hr => firstE9 C hr
  last := fun r hr => lastE9 C hr
  chA := fun r => by
    show Compute.LogUp.limbVal b (EN9 r).chal chalAlphaW = α
    rw [chalE9 C r, C.hα]
  chG := fun r => by
    show Compute.LogUp.limbVal b (EN9 r).chal chalGammaW = γ
    rw [chalE9 C r, C.hγ]
  pIC := fun r => by
    show Compute.LogUp.limbVal b (EN9 r).pub pubIC = α
    rw [pubE9 C r, C.hIC]
  pSeed := fun r => by
    show Compute.LogUp.limbVal b (EN9 r).pub pubSeed = seed
    rw [pubE9 C r, C.hSeed]
  pOut := fun r => by
    show Compute.LogUp.limbVal b (EN9 r).pub pubOut = 0
    rw [pubE9 C r, C.hOut]

/-- The compute walk of an accepted twin trace (`cwalkX9_sat` at `walkRowsX9_of_sat`). -/
theorem cwalkX9_of_sat (C : XCtx hn nodes b δ chalV pubVal orbit P α γ seed)
    (hseed : seed = Walk.rlc γ (encT (K := K) (rowW9 (EN9 0) (stX9 (EN9 0))).trip) * α) :
    ∃ ln cnt acc : ℕ → K,
      Walk.WalkSat (fun i => Walk.rlc γ (enc9 (lblOf9 (rowsWX9 (fun r => EN9 r)
          (fun r => stX9 (EN9 r))) i)))
        (fun i l => Walk.rlc γ (enc9 (clabOf9 (rowsWX9 (fun r => EN9 r) (fun r => stX9 (EN9 r))) i l)))
        (foOf9 (rowsWX9 (fun r => EN9 r) (fun r => stX9 (EN9 r)))) ln cnt acc α
        (∑ i ∈ Finset.Icc 1 1, Walk.rlc γ (enc9 (lblOf9 (rowsWX9 (fun r => EN9 r)
          (fun r => stX9 (EN9 r))) i)) * α ^ i)
        (α ^ 1) n ∧
      acc n = 0 ∧ (∀ i, 1 ≤ i → i < n → cnt i ≠ ln i) ∧ cnt n = ln n :=
  cwalkX9_sat (walkRowsX9_of_sat C) hseed

section Goal
variable [Fintype K] [DecidableEq K]

/-- **The forest goal of the twin compute walk**, outside `tileSet` / `cwEvent9`. -/
theorem goalJ9A (C : XCtx hn nodes b δ chalV pubVal orbit P α γ seed)
    (hseed : seed = Walk.rlc γ (encT (K := K) (rowW9 (EN9 0) (stX9 (EN9 0))).trip) * α)
    (hα : α ∉ tileSet (foOf9 (rowsWX9 (fun r => EN9 r) (fun r => stX9 (EN9 r)))) n)
    (hw : (α, γ) ∉ cwEvent9 (K := K) (rowsWX9 (fun r => EN9 r) (fun r => stX9 (EN9 r))) n) :
    ForestReconGoal (stVS9 K) (lblOf9 (rowsWX9 (fun r => EN9 r) (fun r => stX9 (EN9 r)))) 1 n := by
  obtain ⟨ln, cnt, acc, hsat, hacc, hne, hterm⟩ := cwalkX9_of_sat C hseed
  exact goal_of_not_mem9 _ (tile_of_walk hsat hterm hα) (bfs_of_walk hsat hne) ⟨ln, cnt, acc, hsat, hacc⟩ hw

end Goal

end Chip

end

#print axioms kidsX9_rowW9_of_halving
#print axioms cwalkX9_sat
#print axioms goalJ9A

end Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeX9
