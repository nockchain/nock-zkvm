/-
  Nock/NockVMROM/Thm54/VclL/Handle/WalkBridgeJ8.lean

  **The chip → label bridge of the J-8 compute
  walk** (C-2's open `curLX / childSumX = rlc encT`).  New module, additive.

  * `rowW env st` — the WALK decoding of a row: `rowOfX env st`, except that an `s10L` row is read by
    its committed chip child label `labAtom xS vX xE`, i.e. with the single kid `(s, (0, val vX), e)`
    (shaped as an `s3` row: `ft := (0, val vX)`, `sf1 := e`).  Same `(s, f, e)` as `rowOfX`
    (`rowW_trip`), same fanout (`fanS_rowW`).  When the halving is exact (`HalvingOK`) its kid IS the
    `kidsX` kid of the real row (`kidsX_rowW_of_halving`).  The decoding is a choice of the walk's
    `rows` argument; `cwEvent` (the priced event) is generic in `rows` — its SHAPE does not change.
  * `curLX_eval`, `childrenX_eval`, `ccLX_eval`, `cmLX_eval` — the walk gate's `𝕂` terms evaluate to
    `rlc γ (encT …)` of the decoded handles (`hdV = (val k, val v)`; no smallness hypothesis: decoded
    values are `ZMod.val`).
  * `WalkRowsX` / **`cwalkX_sat`** — an environment sequence satisfying `walkGatesX` row by row (the
    masks, `traceNext` links, the walk coins and publics) gives `Walk.WalkSat` at `rowsWX` (1-indexed)
    with `out = 0`, the queue witness and the terminal count: the input of `WalkTreeVSX.goal_of_not_mem`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HalvingTreeJ8
import Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
import Nock.NockVMROM.Thm54.VclL.Handle.HonestLookups

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8

open Nock Nock.Reified Nock.Edit
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd chalAlphaW chalGammaW pubIC pubSeed pubOut cc notC kv wv)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-! ## 1. The walk decoding -/

/-- **The walk decoding of a row**: `rowOfX`, with an `s10L` row read through its chip child label. -/
def rowW (env : Env (ZMod p)) : StateX → RowVSX
  | .s10L => { rowOfX env .s10L with st := .s3, ft := (0, (env.trace vX).val), sf1 := hdV env xE }
  | st => rowOfX env st

theorem rowW_trip (env : Env (ZMod p)) (st : StateX) : (rowW env st).trip = (rowOfX env st).trip := by
  cases st <;> rfl

theorem fanS_rowW (env : Env (ZMod p)) (st : StateX) : fanS (rowW env st).st = fanS st := by
  cases st <;> rfl

theorem rowW_of_ne (env : Env (ZMod p)) {st : StateX} (h : st ≠ .s10L) : rowW env st = rowOfX env st := by
  cases st <;> first | rfl | exact absurd rfl h

theorem kidsX_rowW_s10L (env : Env (ZMod p)) :
    kidsX (rowW env .s10L) = [(hdV env xS, (0, (env.trace vX).val), hdV env xE)] := rfl

/-- **Exact halving ⇒ the chip kid is the `kidsX` kid** (`f.v = 2 v + β`, no wrap). -/
theorem kidsX_rowW_of_halving {env : Env (ZMod p)} (hB : BaseHoldsX env) (hOH : OneHotAt env 12)
    (hv : HalvingOK env .s10L) : kidsX (rowW env .s10L) = kidsX (rowOfX env .s10L) := by
  obtain ⟨hv1, hv2⟩ := hv rfl
  obtain ⟨-, hfv, -⟩ := s10L_row hB (oh_one hOH (by decide)) (oh_zero hOH (by decide) (by decide))
    (oh_zero hOH (by decide) (by decide))
  have hβ := col_bool hB (i := betaX) (by simp [oneHotG])
  rw [kidsX_rowW_s10L]
  simp only [kidsX, rowOfX, hdV, List.cons.injEq, Prod.mk.injEq, and_true, true_and]
  simp only [tr] at hfv
  rcases hβ with h0 | h1
  · rw [hfv, h0, add_zero]
    have : ((2 : ZMod p) * env.trace vX) = ((2 * (env.trace vX).val : ℕ) : ZMod p) := by
      push_cast; rw [ZMod.natCast_zmod_val]
    rw [this, ZMod.val_natCast_of_lt (by omega)]
    omega
  · rw [hfv, h1]
    have : ((2 : ZMod p) * env.trace vX + 1) = ((2 * (env.trace vX).val + 1 : ℕ) : ZMod p) := by
      push_cast; rw [ZMod.natCast_zmod_val]
    rw [this, ZMod.val_natCast_of_lt (by omega)]
    omega

/-- Every decoded handle value is below `p`. -/
theorem smallR_rowW (env : Env (ZMod p)) (st : StateX) : SmallR p (rowW env st) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have g : ∀ h : Hd, (hdV env h).1 < p ∧ (hdV env h).2 < p := fun h =>
    ⟨ZMod.val_lt _, ZMod.val_lt _⟩
  intro h hh
  cases st <;>
    simp only [rowW, rowOfX, List.mem_cons, List.not_mem_nil, or_false] at hh <;>
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact g _ | exact ⟨hp, ZMod.val_lt _⟩

theorem childrenX_len (st : StateX) : (childrenX (stIdx st)).length = fanS st := by
  cases st <;> rfl

theorem zipIdx_sum' {α M : Type} [AddCommMonoid M] (d : α) (g : α → ℕ → M) :
    ∀ (l : List α) (k : ℕ), ((l.zipIdx k).map fun p => g p.1 p.2).sum =
      ∑ i ∈ Finset.range l.length, g (l.getD i d) (k + i)
  | [], k => by simp
  | a :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, zipIdx_sum' d g l (k + 1), List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show k + 1 + c = k + (c + 1) by omega]

/-! ## 2. The walk gate's `𝕂` terms -/

section Eval
variable {K : Type} [Field K] [Algebra (ZMod p) K]

open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (sumM)

theorem alg_val (x : ZMod p) : ((x.val : ℕ) : K) = algebraMap (ZMod p) K x := by
  rw [← map_natCast (algebraMap (ZMod p) K), ZMod.natCast_zmod_val]

variable (eK : Env K) (eF : Env (ZMod p)) (kind : VarKind) (e' : Env (ZMod p))
  (hk : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF = e'.trace i)
include hk

theorem lab_eval (γ : ℕ) (s f e : Hd) :
    evalMQ (rlcKeyL kind γ 0 (labX s f e) : MixedExpr ℚ) eK eF =
      Walk.rlc (eK.chal γ) (encT (K := K) (hdV e' s, hdV e' f, hdV e' e)) := by
  simp only [labX, rlcKeyL, evalMQ, hk, Walk.rlc, Fin.sum_univ_succ, encT, encH, hdV, alg_val,
    Fin.sum_univ_zero]
  simp

theorem labAtom_eval (γ : ℕ) (s : Hd) (fv : ℕ) (e : Hd) :
    evalMQ (rlcKeyL kind γ 0 (labAtom s fv e) : MixedExpr ℚ) eK eF =
      Walk.rlc (eK.chal γ) (encT (K := K) (hdV e' s, (0, (e'.trace fv).val), hdV e' e)) := by
  simp only [labAtom, rlcKeyL, evalMQ, hk, Walk.rlc, Fin.sum_univ_succ, encT, encH, hdV, alg_val,
    Fin.sum_univ_zero]
  simp

theorem curLX_eval (st : StateX) :
    evalMQ (curLX kind : MixedExpr ℚ) eK eF =
      Walk.rlc (eK.chal chalGammaW) (encT (K := K) (rowW e' st).trip) := by
  rw [rowW_trip]
  exact lab_eval eK eF kind e' hk _ _ _ _

theorem childrenX_eval (γ : ℕ) (st : StateX) (i : ℕ) (hi : i < fanS st) :
    evalMQ (rlcKeyL kind γ 0 ((childrenX (stIdx st)).getD i []) : MixedExpr ℚ) eK eF =
      Walk.rlc (eK.chal γ) (encT (K := K) ((kidsX (rowW e' st)).getD i trip0)) := by
  have l := lab_eval eK eF kind e' hk γ
  have a := labAtom_eval eK eF kind e' hk γ
  cases st <;> simp only [fanS] at hi <;> (try omega) <;> interval_cases i <;>
    simp only [childrenX, stIdx, kidsX, rowW, rowOfX, List.getD_cons_zero, List.getD_cons_succ, l, a]

omit hk in
theorem evalMQ_sumM' (l : List (MixedExpr ℚ)) :
    evalMQ (sumM l : MixedExpr ℚ) eK eF = (l.map fun u => evalMQ u eK eF).sum := by
  induction l with
  | nil => simp [sumM, evalMQ]
  | cons a l ih => simp only [sumM, List.foldr_cons] at ih ⊢; simp [evalMQ, ih]

omit hk in
theorem sum_onehotX (X : ℕ → K) (st : StateX) (hOH : OneHotAt e' (stIdx st)) :
    ((List.range nStates).map fun j => algebraMap (ZMod p) K (e'.trace j) * X j).sum = X (stIdx st) := by
  have : (List.range nStates).map (fun j => algebraMap (ZMod p) K (e'.trace j) * X j) =
      (List.range nStates).map (fun j => if j = stIdx st then X j else 0) :=
    List.map_congr_left fun j hj => by
      rw [hOH j (List.mem_range.mp hj)]; split_ifs <;> simp
  rw [this]
  cases st <;> simp [List.range_succ, nStates, stIdx]

theorem ccLX_eval (st : StateX) (hOH : OneHotAt e' (stIdx st)) :
    evalMQ (ccLX kind : MixedExpr ℚ) eK eF =
      ∑ i ∈ Finset.range (fanS st), eK.chal chalAlphaW ^ (i + 1) *
        Walk.rlc (eK.chal chalGammaW) (encT (K := K) ((kidsX (rowW e' st)).getD i trip0)) := by
  unfold ccLX
  rw [evalMQ_sumM', List.map_map]
  have h1 : ∀ j, evalMQ (MixedExpr.Scale (kv kind j) (childSumX kind j) : MixedExpr ℚ) eK eF =
      algebraMap (ZMod p) K (e'.trace j) * evalMQ (childSumX kind j : MixedExpr ℚ) eK eF := by
    intro j; simp only [evalMQ, kv, hk]
  simp only [Function.comp_def, h1, allStatesX]
  rw [sum_onehotX (e' := e') (fun j => evalMQ (childSumX kind j : MixedExpr ℚ) eK eF) st hOH]
  unfold childSumX
  rw [evalMQ_sumM', List.map_map]
  have h2 : ∀ q : List (Option ℕ) × ℕ, evalMQ (MixedExpr.Mul (MixedExpr.Pow
      (MixedExpr.Var .challenge chalAlphaW) (q.2 + 1)) (rlcKeyL kind chalGammaW 0 q.1) : MixedExpr ℚ) eK eF =
      eK.chal chalAlphaW ^ (q.2 + 1) * evalMQ (rlcKeyL kind chalGammaW 0 q.1 : MixedExpr ℚ) eK eF := by
    intro q; simp only [evalMQ]
  simp only [Function.comp_def, h2]
  rw [zipIdx_sum' [] (fun q1 q2 => eK.chal chalAlphaW ^ (q2 + 1) *
    evalMQ (rlcKeyL kind chalGammaW 0 q1 : MixedExpr ℚ) eK eF) (childrenX (stIdx st)) 0, childrenX_len]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [childrenX_eval eK eF kind e' hk chalGammaW st i (Finset.mem_range.mp hi), zero_add]

theorem cmLX_eval (st : StateX) (hOH : OneHotAt e' (stIdx st)) :
    evalMQ (cmLX kind : MixedExpr ℚ) eK eF = eK.chal chalAlphaW ^ (fanS st) := by
  unfold cmLX
  rw [evalMQ_sumM', List.map_map]
  have h1 : ∀ j, evalMQ (MixedExpr.Scale (kv kind j) (MixedExpr.Pow (MixedExpr.Var .challenge chalAlphaW)
      (childrenX j).length) : MixedExpr ℚ) eK eF =
      algebraMap (ZMod p) K (e'.trace j) * eK.chal chalAlphaW ^ (childrenX j).length := by
    intro j; simp only [evalMQ, kv, hk]
  simp only [Function.comp_def, h1, allStatesX]
  rw [sum_onehotX (e' := e') (fun j => eK.chal chalAlphaW ^ (childrenX j).length) st hOH, childrenX_len]

end Eval


/-! ## 3. The compute walk over an accepted row sequence -/

section Seq
variable {K : Type} [Field K] [Algebra (ZMod p) K]

/-- **An accepted compute-walk row sequence** (`n` chip rows; walk row `i` = chip row `i − 1`): the base
environment `E r` (row `r`, its `traceNext` is row `r + 1`), the `𝕂` environment `EK r` (the walk
columns, coins, publics), the decoded state `st r` (one-hot), the nine `walkGatesX` at every row,
the `isFirst` / `isLast` masks, the walk coins `αW = α`, `γW = γ`, the publics `IC = α`, `seed`,
`out = 0`. -/
structure WalkRowsX (n : ℕ) (E : ℕ → Env (ZMod p)) (EK : ℕ → Env K) (st : ℕ → StateX)
    (α γ seed : K) : Prop where
  hn : 0 < n
  oh : ∀ r < n, OneHotAt (E r) (stIdx (st r))
  gate : ∀ r < n, ∀ g ∈ (walkGatesX : List (MixedExpr ℚ)), evalMQ g (EK r) (E r) = 0
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
def rowsWX (E : ℕ → Env (ZMod p)) (st : ℕ → StateX) (i : ℕ) : RowVSX := rowW (E (i - 1)) (st (i - 1))

variable {n : ℕ} {E : ℕ → Env (ZMod p)} {EK : ℕ → Env K} {st : ℕ → StateX} {α γ seed : K}
  (C : WalkRowsX n E EK st α γ seed)
include C

theorem lastZ {r : ℕ} (hr : r + 1 < n) : (E r).trace lastX = 0 := by
  rw [C.last r (by omega)]; simp; omega

theorem hkN {r : ℕ} (hr : r + 1 < n) :
    ∀ i, evalQ (.var .traceNext i : CoeffExpr ℚ) (E r) = (E (r + 1)).trace i := fun i => by
  show (E r).traceNext i = _
  rw [C.next r hr]

theorem gX {r : ℕ} (hr : r < n) (k : ℕ) (hk : k < 9) :
    evalMQ ((walkGatesX : List (MixedExpr ℚ))[k]'(by simp [walkGatesX]; omega)) (EK r) (E r) = 0 :=
  C.gate r hr _ (List.getElem_mem _)

theorem w_ln_step {r : ℕ} (hr : r + 1 < n) :
    (EK (r + 1)).trace wLnX = α * (EK r).trace wLnX := by
  have h0 := gX C (by omega : r < n) 0 (by norm_num)
  simp [walkGatesX, evalMQ, evalQ, notC, cc, ChipH.wv, lastZ C hr, C.nextK r hr, C.chA r,
    sub_eq_zero] at h0
  exact h0

theorem w_cnt_step {r : ℕ} (hr : r + 1 < n) :
    (EK (r + 1)).trace wCntX = (EK r).trace wCntX * α ^ (fanS (st (r + 1))) := by
  have h0 := gX C (by omega : r < n) 1 (by norm_num)
  have hc := cmLX_eval (EK r) (E r) .traceNext (E (r + 1)) (hkN C hr) (st (r + 1)) (C.oh _ hr)
  simp only [walkGatesX, List.getElem_cons_succ, List.getElem_cons_zero, evalMQ, ChipH.wv, hc] at h0
  simp [evalQ, notC, cc, lastZ C hr, C.nextK r hr, C.chA r, sub_eq_zero] at h0
  exact h0

theorem w_acc_step {r : ℕ} (hr : r + 1 < n) :
    (EK (r + 1)).trace wLnX * Walk.rlc γ (encT (K := K) (rowW (E (r + 1)) (st (r + 1))).trip) +
      (EK (r + 1)).trace wAccX - (EK r).trace wAccX =
    ∑ i ∈ Finset.range (fanS (st (r + 1))), (EK r).trace wCntX *
      (α ^ (i + 1) * Walk.rlc γ (encT (K := K) ((kidsX (rowW (E (r + 1)) (st (r + 1)))).getD i trip0))) := by
  have h0 := gX C (by omega : r < n) 2 (by norm_num)
  have hc := ccLX_eval (EK r) (E r) .traceNext (E (r + 1)) (hkN C hr) (st (r + 1)) (C.oh _ hr)
  have hl := curLX_eval (EK r) (E r) .traceNext (E (r + 1)) (hkN C hr) (st (r + 1))
  rw [C.chA r, C.chG r] at hc
  rw [C.chG r] at hl
  simp only [walkGatesX, List.getElem_cons_succ, List.getElem_cons_zero, evalMQ, ChipH.wv, hc, hl] at h0
  simp [evalQ, notC, cc, lastZ C hr, C.nextK r hr] at h0
  rw [← Finset.mul_sum]
  exact sub_eq_zero.mp h0

theorem first0 : (E 0).trace firstX = 1 := by rw [C.first 0 C.hn]; simp

theorem w_ln_zero : (EK 0).trace wLnX = α := by
  have h0 := gX C C.hn 3 (by norm_num)
  simp [walkGatesX, evalMQ, evalQ, cc, ChipH.wv, first0 C, C.chA 0, sub_eq_zero] at h0
  exact h0

theorem w_cnt_zero : (EK 0).trace wCntX = α * α ^ (fanS (st 0)) := by
  have h0 := gX C C.hn 4 (by norm_num)
  have hc := cmLX_eval (EK 0) (E 0) .traceCur (E 0) (fun _ => rfl) (st 0) (C.oh 0 C.hn)
  rw [C.chA 0] at hc
  simp only [walkGatesX, List.getElem_cons_succ, List.getElem_cons_zero, evalMQ, ChipH.wv, hc] at h0
  simp [evalQ, cc, first0 C, C.pIC 0, sub_eq_zero] at h0
  exact h0

theorem w_acc_zero :
    (EK 0).trace wLnX * Walk.rlc γ (encT (K := K) (rowW (E 0) (st 0)).trip) + (EK 0).trace wAccX =
    α * ∑ i ∈ Finset.range (fanS (st 0)),
      (α ^ (i + 1) * Walk.rlc γ (encT (K := K) ((kidsX (rowW (E 0) (st 0))).getD i trip0))) + seed := by
  have h0 := gX C C.hn 5 (by norm_num)
  have hc := ccLX_eval (EK 0) (E 0) .traceCur (E 0) (fun _ => rfl) (st 0) (C.oh 0 C.hn)
  have hl := curLX_eval (EK 0) (E 0) .traceCur (E 0) (fun _ => rfl) (st 0)
  rw [C.chA 0, C.chG 0] at hc
  rw [C.chG 0] at hl
  simp only [walkGatesX, List.getElem_cons_succ, List.getElem_cons_zero, evalMQ, ChipH.wv, hc, hl] at h0
  simp [evalQ, cc, first0 C, C.pIC 0, C.pSeed 0] at h0
  exact sub_eq_zero.mp h0

theorem w_wit {r : ℕ} (hr : r + 1 < n) : (EK r).trace wCntX ≠ (EK r).trace wLnX := by
  have h0 := gX C (by omega : r < n) 6 (by norm_num)
  simp [walkGatesX, evalMQ, evalQ, notC, cc, ChipH.wv, lastZ C hr, sub_eq_zero] at h0
  intro he
  rw [he, sub_self, mul_zero] at h0
  exact zero_ne_one h0

theorem w_last : (EK (n - 1)).trace wCntX = (EK (n - 1)).trace wLnX ∧ (EK (n - 1)).trace wAccX = 0 := by
  have hr : n - 1 < n := by have := C.hn; omega
  have m : (E (n - 1)).trace lastX = 1 := by rw [C.last _ hr]; simp
  have h7 := gX C hr 7 (by norm_num)
  have h8 := gX C hr 8 (by norm_num)
  simp [walkGatesX, evalMQ, evalQ, cc, ChipH.wv, m, sub_eq_zero, C.pOut] at h7 h8
  exact ⟨h7, h8⟩

omit C in
theorem sum_Icc_range' {M : Type} [AddCommMonoid M] (f : ℕ → M) :
    ∀ m : ℕ, ∑ l ∈ Finset.Icc 1 m, f l = ∑ i ∈ Finset.range m, f (i + 1)
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, sum_Icc_range' f m]

omit C in
theorem foOf_rowsWX (i : ℕ) : foOf (rowsWX E st) i = fanS (st (i - 1)) := by
  simp [foOf, rowsWX, fanS_rowW]

/-- **The compute walk of `computeChipVCLHX`, chip → label bridge**: an accepted row sequence is a
`Walk.WalkSat` over the walk-decoded rows `rowsWX` (labels `rlc γ (enc …)`, the committed child labels,
`initial_count = α`, seed `= rlc γ (label of row 1)·α`), with `out = 0`, the queue witness and the
terminal count — the input of `WalkTreeVSX.goal_of_not_mem` / `bfs_of_walk` / `tile_of_walk`. -/
theorem cwalkX_sat
    (hseed : seed = Walk.rlc γ (encT (K := K) (rowW (E 0) (st 0)).trip) * α) :
    ∃ ln cnt acc : ℕ → K,
      Walk.WalkSat (fun i => Walk.rlc γ (enc (lblOf (rowsWX E st) i)))
        (fun i l => Walk.rlc γ (enc (clabOf (rowsWX E st) i l)))
        (foOf (rowsWX E st)) ln cnt acc α
        (∑ i ∈ Finset.Icc 1 1, Walk.rlc γ (enc (lblOf (rowsWX E st) i)) * α ^ i)
        (α ^ 1) n ∧
      acc n = 0 ∧ (∀ i, 1 ≤ i → i < n → cnt i ≠ ln i) ∧ cnt n = ln n := by
  have encL : ∀ i, enc (K := K) (lblOf (rowsWX E st) i) = encT (rowW (E (i - 1)) (st (i - 1))).trip :=
    fun _ => rfl
  have encC : ∀ i l, enc (K := K) (clabOf (rowsWX E st) i l) =
      encT ((kidsX (rowW (E (i - 1)) (st (i - 1)))).getD (l - 1) trip0) := by
    intro i l; simp [WalkLblVSX.enc, clabOf, rowsWX]
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
    · rw [pow_one, foOf_rowsWX]; exact w_cnt_zero C
    · obtain ⟨r, rfl⟩ : ∃ r, i = r + 1 := ⟨i - 1, by omega⟩
      simp only [foOf_rowsWX, Nat.add_sub_cancel]
      exact w_cnt_step C (r := r) (by omega)
    · have h0 := w_acc_zero C
      simp only [Finset.Icc_self, Finset.sum_singleton]
      rw [sum_Icc_range', foOf_rowsWX]
      simp only [pow_one, encL, encC, Nat.reduceSub, Nat.sub_self]
      rw [← hseed, h0, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Nat.add_sub_cancel]
      ring
    · obtain ⟨r, rfl⟩ : ∃ r, i = r + 1 := ⟨i - 1, by omega⟩
      have h0 := w_acc_step C (r := r) (by omega)
      rw [sum_Icc_range', foOf_rowsWX]
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


/-! ## 4. The tree: `HalvingOK` from the tree, then `HoldsN` -/

section Tree
open Nock.Walk Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.HalvingTreeJ8 (halvingOK_of_child)
variable {K : Type} [Field K]

/-- **The per-row hypotheses** of the extraction: base gates, the one-hot state, the served genuine
records (`RecOK`, step 3 discharges them per kind) and, on `s10L` rows, the sibling-read axis in
`[2, 2^62)` (`WalkJ8.walkJ8_axis_lt` for a record served by the walk balance; step 3). -/
structure RowsAccX (n : ℕ) (E : ℕ → Env (ZMod p)) (st : ℕ → StateX) (D : HX → Option Noun)
    (R : Nock.Jet.Registry) (limbA : ℕ → ℕ → HX) : Prop where
  base : ∀ r < n, BaseHoldsX (E r)
  oh : ∀ r < n, OneHotAt (E r) (stIdx (st r))
  served : ∀ r < n, ∀ x ∈ activeX (E r), RecOK D R limbA x
  ax : ∀ r < n, st r = .s10L → 2 ≤ ((E r).trace xM.v).val ∧ ((E r).trace xM.v).val < 2 ^ 62

variable {n : ℕ} {E : ℕ → Env (ZMod p)} {st : ℕ → StateX} {D : HX → Option Noun}
  {R : Nock.Jet.Registry} {limbA : ℕ → ℕ → HX}

/-- **`HalvingOK` at every `s10L` node of the walk tree**: the node's one child carries the chip
child label `(s, (0, v), e)`, the child is some row (label link `xF = (0, v)`), and
`halvingOK_of_child` applies. -/
theorem halving_of_tree (hp : 2 ^ 63 + 1 < p) (A : RowsAccX n E st D R limbA)
    {t : NTree (StateX × RowVSX)}
    (hrow : ∀ u, InTree t u → ∃ i, 1 ≤ i ∧ i ≤ n ∧ u.label = lblOf (rowsWX E st) i)
    (hlink : ∀ u, InTree t u → u.children.map (fun c => c.label.2.trip) = kidsX u.label.2)
    {u : NTree (StateX × RowVSX)} (hu : InTree t u) {i : ℕ} (hui : u.label = lblOf (rowsWX E st) i)
    (hs : st (i - 1) = .s10L) : HalvingOK (E (i - 1)) .s10L := by
  have hl := hlink u hu
  rw [hui] at hl
  simp only [lblOf, rowsWX, hs, kidsX_rowW_s10L] at hl
  have hlen := congrArg List.length hl
  simp only [List.length_map, List.length_cons, List.length_nil] at hlen
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp hlen
  rw [hc] at hl
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hl
  have hcin : InTree t c := inTree_trans hu (InTree.sub (by rw [hc]; simp) (InTree.here _))
  obtain ⟨j, hj1, hjn, hcj⟩ := hrow c hcin
  rw [hcj] at hl
  simp only [lblOf, rowsWX] at hl
  rw [rowW_trip] at hl
  simp only [rowOfX, RowVSX.trip, hdV, Prod.mk.injEq] at hl
  obtain ⟨-, ⟨hk, hv⟩, -⟩ := hl
  exact halvingOK_of_child hp (A.base _ (by omega)) (A.oh _ (by omega)) (ZMod.val_eq_zero _ |>.mp hk)
    (ZMod.val_injective _ hv) (A.ax _ (by omega))

/-- **J-8a step 1 + step 3 (halving part) composed**: an accepted compute walk (`ForestReconGoal` over
the walk-decoded rows `rowsWX`, i.e. outside `cwEvent` with `cwalkX_sat`'s facts) whose rows satisfy
`RowsAccX` and whose root is a real row denoting the claim proves `HoldsN` of the claim.  No
`HalvingOK` hypothesis: it is derived from the tree (`halving_of_tree`). -/
theorem holdsN_of_walkJ8 [CharP K p] (hp : 2 ^ 63 + 1 < p) (hR : R.Faithful) (hD : DenOKX p D)
    (hn : 1 ≤ n) (A : RowsAccX n E st D R limbA)
    (hG : ForestReconGoal (stVS K) (lblOf (rowsWX E st)) 1 n)
    (hreal : (st 0).isChain = false) (x : P8PublicClaim)
    (hs : D (hdV (E 0) xS) = some x.subject) (hf : D (hdV (E 0) xF) = some x.formula)
    (he : D (hdV (E 0) xE) = some x.result) : Nock.Jet.HoldsN x := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨t, hroot, hrow, hlink⟩ :=
    tree_of_goal (K := K) p hp0 (rowsWX E st) hn (fun i _ _ => smallR_rowW _ _) hG
  let rw : StateX × RowVSX → RowVSX := fun l =>
    if h : ∃ i, 1 ≤ i ∧ i ≤ n ∧ l = lblOf (rowsWX E st) i then
      rowOfX (E (Nat.find h - 1)) (st (Nat.find h - 1)) else l.2
  have rw_spec : ∀ u, InTree t u → ∃ i, 1 ≤ i ∧ i ≤ n ∧ u.label = lblOf (rowsWX E st) i ∧
      rw u.label = rowOfX (E (i - 1)) (st (i - 1)) := by
    intro u hu
    have h := hrow u hu
    exact ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2.1, (Nat.find_spec h).2.2,
      by simp only [rw, dif_pos h]⟩
  have hrt : rw t.label = rowOfX (E 0) (st 0) := by
    have h : ∃ i, 1 ≤ i ∧ i ≤ n ∧ t.label = lblOf (rowsWX E st) i := ⟨1, le_rfl, hn, hroot⟩
    have h1 : Nat.find h = 1 := le_antisymm (Nat.find_min' h ⟨le_rfl, hn, hroot⟩) (Nat.find_spec h).1
    simp only [rw, dif_pos h, h1]
  have hok : RowsOKX rw p D R t := by
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · obtain ⟨i, hi1, hin, hui, hrw⟩ := rw_spec u hu
      rw [hrw]
      exact rowSemX_of_chip hD (by omega) (A.base _ (by omega)) (st (i - 1)) (A.oh _ (by omega))
        (A.served _ (by omega)) (fun hs => halving_of_tree hp A hrow hlink hu hui hs rfl)
    · obtain ⟨i, hi1, hin, hui, hrw⟩ := rw_spec u hu
      have hm : u.children.map (fun c => (rw c.label).trip) = u.children.map (fun c => c.label.2.trip) :=
        List.map_congr_left fun c hc => by
          obtain ⟨j, -, -, hcj, hrwc⟩ := rw_spec c (inTree_trans hu (InTree.sub hc (InTree.here _)))
          rw [hrwc, hcj]
          simp only [lblOf, rowsWX, rowW_trip]
      rw [hm, hlink u hu, hrw, hui]
      simp only [lblOf, rowsWX]
      by_cases hs : st (i - 1) = .s10L
      · have hH := halving_of_tree hp A hrow hlink hu hui hs
        have hO := A.oh (i - 1) (by omega)
        rw [hs] at hO ⊢
        exact kidsX_rowW_of_halving (A.base _ (by omega)) hO hH
      · rw [rowW_of_ne _ hs]
  exact holdsN_of_rowsVSX rw hR hD t hok (by rw [hrt]; exact hreal) x (by rw [hrt]; exact hs)
    (by rw [hrt]; exact hf) (by rw [hrt]; exact he)

end Tree

end

end Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
