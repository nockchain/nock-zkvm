/-
  Nock/NockVMROM/Thm54/VclL/Handle/WalkGatesH.lean

  Additive.

  * `walkGates_hold`: the nine `𝕂` gates of `ChipH.walkGates` vanish on a row whose columns are the closed
    forms of `walkSat_closed` (`WalkSat` + tiling + perfect completeness + queue non-emptiness);
  * `curL_honest` / `childSum_honest` / `ccL_honest` / `cmL_honest`: the label RLC, the per-state child sum, the
    one-hot-selected child sum and the count multiplier read off the honest handle row (`colVal`), as RLCs of
    the handles of `childNouns` (`ChildLinkH`);
  * `cc_link` / `reads_at`: the queue side of the child link: `Σ_l α^l chld(i, l)` at handle labels is the
    row's `ccL` read (from `child_link_nouns`, i.e. `childrenMatchSf` + the generator induction);
  * `walkGatesH_honest`: every gate at every BFS row `1 ≤ i ≤ h` of the committed tree, at `walkEnvK/F`.
    Hypothesis `h ≤ orderOf α` (priced in `WalkCoin.walk_coin_order_few`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ChildLinkH
import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestT
import Nock.NockVMROM.Thm54.VclL.Handle.HonestRowsH

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun Nock.Walk Nock.Reified Module
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.TraceGen ComputeTable Nock.NockVMROM.Thm54.SemanticStrategy

noncomputable section

section Gates
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **What a row of the walk reads** (the values the gates are evaluated at): the current row's label,
child sum and count multiplier; the next row's, when there is one. -/
structure RowReads (eK : Env K) (eF : Env F) (cur ccC cmC : K) (hasNext : Prop) (curN ccN cmN : K) :
    Prop where
  curC : evalMQ (curL (F := ℚ) .traceCur) eK eF = cur
  ccC : evalMQ (ccL (F := ℚ) .traceCur) eK eF = ccC
  cmC : evalMQ (cmL (F := ℚ) .traceCur) eK eF = cmC
  nxt : hasNext → evalMQ (curL (F := ℚ) .traceNext) eK eF = curN ∧
    evalMQ (ccL (F := ℚ) .traceNext) eK eF = ccN ∧ evalMQ (cmL (F := ℚ) .traceNext) eK eF = cmN

theorem evalMQ_scale (g : CoeffExpr ℚ) (u : MixedExpr ℚ) (eK : Env K) (eF : Env F) :
    evalMQ (.Scale g u) eK eF = algebraMap F K (evalQ g eF) * evalMQ u eK eF := rfl

theorem evalQ_notC (i : ℕ) (eF : Env F) : evalQ (notC (F := ℚ) i) eF = 1 - eF.trace i := by
  simp [notC, cc, evalQ]

theorem evalQ_cc (i : ℕ) (eF : Env F) : evalQ (cc (F := ℚ) i) eF = eF.trace i := by
  simp [cc, evalQ]

/-- **The nine compute-walk gates vanish on a row whose columns are the closed-form walk.**  Row `i`
(`1`-based) of `h`; `first / last` flags; `WalkSat` supplies the recurrences; the boundary facts are the
tiling (`cnt h = ln h`), perfect completeness (`acc h = out`) and queue non-emptiness (`cnt i ≠ ln i`,
`i < h`, the `h ≤ orderOf α` honest-bad condition). -/
theorem walkGates_hold {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {ln cnt acc : ℕ → K}
    {α seed : K} {h : ℕ}
    (hw : Walk.WalkSat cur chld' fo ln cnt acc α seed α h)
    (eK : Env K) (eF : Env F) (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ h)
    (hα : eK.chal chalAlphaW = α) (hIC : eK.pub pubIC = α) (hseed : eK.pub pubSeed = seed)
    (hlnC : eK.trace wLn = ln i) (hlnN : eK.traceNext wLn = ln (i + 1))
    (hcnC : eK.trace wCnt = cnt i) (hcnN : eK.traceNext wCnt = cnt (i + 1))
    (hacC : eK.trace wAcc = acc i) (hacN : eK.traceNext wAcc = acc (i + 1))
    (hinv : i < h → eK.trace wInv * (cnt i - ln i) = 1)
    (hfirst : eF.trace firstCol = if i = 1 then 1 else 0)
    (hlast : eF.trace lastCol = if i = h then 1 else 0)
    (hout : eK.pub pubOut = acc h) (hcntlast : cnt h = ln h)
    (hrd : RowReads eK eF (cur i) (∑ l ∈ Finset.Icc 1 (fo i), α ^ l * chld' i l) (α ^ fo i)
      (i < h) (cur (i + 1)) (∑ l ∈ Finset.Icc 1 (fo (i + 1)), α ^ l * chld' (i + 1) l)
      (α ^ fo (i + 1))) :
    ∀ g ∈ (walkGates : List (MixedExpr ℚ)), evalMQ g eK eF = 0 := by
  intro g hg
  have hnl : algebraMap F K (evalQ (notLast (F := ℚ)) eF) = if i = h then 0 else 1 := by
    simp only [notLast, evalQ_notC, hlast]; split <;> simp
  have hfl : algebraMap F K (evalQ (cc (F := ℚ) firstCol) eF) = if i = 1 then 1 else 0 := by
    simp only [evalQ_cc, hfirst]; split <;> simp
  have hll : algebraMap F K (evalQ (cc (F := ℚ) lastCol) eF) = if i = h then 1 else 0 := by
    simp only [evalQ_cc, hlast]; split <;> simp
  simp only [walkGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  have ev : ∀ (a : CoeffExpr ℚ) (u : MixedExpr ℚ), evalMQ (.Scale a u) eK eF =
      algebraMap F K (evalQ a eF) * evalMQ u eK eF := fun a u => rfl
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ev, hnl]
    by_cases hih' : i = h
    · simp [hih']
    · have := hw.lnInc i hi1 (by omega)
      simp [evalMQ, ChipH.wv, hih', hα, hlnC, hlnN, this]
  · rw [ev, hnl]
    by_cases hih' : i = h
    · simp [hih']
    · have := hw.countInc i hi1 (by omega)
      simp [evalMQ, ChipH.wv, hih', hcnC, hcnN, (hrd.nxt (by omega)).2.2, this]
  · rw [ev, hnl]
    by_cases hih' : i = h
    · simp [hih']
    · have := hw.accStep i hi1 (by omega)
      have hs : cnt i * ∑ l ∈ Finset.Icc 1 (fo (i + 1)), α ^ l * chld' (i + 1) l =
          ∑ l ∈ Finset.Icc 1 (fo (i + 1)), α ^ l * cnt i * chld' (i + 1) l := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
      simp only [evalMQ, ChipH.wv, hih', if_false, one_mul, hlnN, hacN, hacC, hcnC, (hrd.nxt (by omega)).1, (hrd.nxt (by omega)).2.1]
      rw [hs]; linear_combination this
  · rw [ev, hfl]
    by_cases hi' : i = 1
    · subst hi'; simp [evalMQ, ChipH.wv, hα, hlnC, hw.ln1]
    · simp [hi']
  · rw [ev, hfl]
    by_cases hi' : i = 1
    · subst hi'; simp [evalMQ, ChipH.wv, hIC, hcnC, hrd.cmC, hw.count1]
    · simp [hi']
  · rw [ev, hfl]
    by_cases hi' : i = 1
    · subst hi'
      have := hw.accInit
      have hs : α * ∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * chld' 1 l =
          ∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * α * chld' 1 l := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
      simp only [evalMQ, ChipH.wv, if_true, one_mul, hlnC, hacC, hIC, hseed, hrd.curC, hrd.ccC]
      rw [hs]; linear_combination this
    · simp [hi']
  · rw [ev, hnl]
    by_cases hih' : i = h
    · simp [hih']
    · have := hinv (by omega)
      simp [evalMQ, ChipH.wv, hih', hcnC, hlnC, this]
  · rw [ev, hll]
    by_cases hih' : i = h
    · subst hih'; simp [evalMQ, ChipH.wv, hcnC, hlnC, hcntlast]
    · simp [hih']
  · rw [ev, hll]
    by_cases hih' : i = h
    · subst hih'; simp [evalMQ, ChipH.wv, hacC, hout]
    · simp [hih']

end Gates

/-! ## 2. The honest reads -/

section Reads
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- RLC of a list of values by a coin `g`, powers from `n`. -/
def rlcL (g : K) : ℕ → List K → K
  | _, [] => 0
  | n, v :: vs => g ^ n * v + rlcL g (n + 1) vs

/-- The six label values of a noun triple, as handles. -/
def hl (cells : List Noun) (t : Noun × Noun × Noun) : List F :=
  [(hdl cells t.1).1, (hdl cells t.1).2, (hdl cells t.2.1).1, (hdl cells t.2.1).2,
   (hdl cells t.2.2).1, (hdl cells t.2.2).2]

/-- The RLC of the handle label of a noun triple at the walk coin `γ`. -/
def lblVal (γ : K) (cells : List Noun) (t : Noun × Noun × Noun) : K :=
  rlcL γ 0 ((hl (F := F) cells t).map (algebraMap F K))

theorem evalMQ_rlcKey (kind : VarKind) (γ : ℕ) (eK : Env K) (eF : Env F) (vals : ℕ → F)
    (hv : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF = vals i) :
    ∀ (n : ℕ) (r : List ℕ), evalMQ (rlcKey (F := ℚ) kind γ n r) eK eF =
      rlcL (eK.chal γ) n (r.map fun i => algebraMap F K (vals i)) := by
  intro n r
  induction r generalizing n with
  | nil => simp [rlcKey, evalMQ, rlcL]
  | cons i r ih =>
    simp only [rlcKey, evalMQ, rlcL, List.map_cons, ih, hv]

end Reads

section Honest
variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable (cells : List Noun) (r : RowN) (fst lst : F) (kind : VarKind) (eK : Env K) (eF : Env F)

theorem hn_s (r : RowN) : (hn r).s = r.s := by unfold hn; split <;> rfl
theorem hn_f (r : RowN) : (hn r).f = r.f := by unfold hn; split <;> rfl
theorem hn_e (r : RowN) : (hn r).e = r.e := by unfold hn; split <;> rfl
theorem hn_sf1 (r : RowN) : (hn r).sf1 = r.sf1 := by unfold hn; split <;> rfl
theorem hn_sf2 (r : RowN) : (hn r).sf2 = r.sf2 := by unfold hn; split <;> rfl
theorem hn_fh (r : RowN) : (hn r).fh = r.fh := by unfold hn; split <;> rfl
theorem hn_ft (r : RowN) : (hn r).ft = r.ft := by unfold hn; split <;> rfl
theorem hn_fth (r : RowN) : (hn r).fth = r.fth := by unfold hn; split <;> rfl
theorem hn_ftt (r : RowN) : (hn r).ftt = r.ftt := by unfold hn; split <;> rfl
theorem hn_m6 (r : RowN) (h : r.op ≠ 5) : (hn r).m = r.m := by rw [hn_of_ne r h]

theorem curL_honest (hcol : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF = colVal cells r fst lst i) :
    evalMQ (curL (F := ℚ) kind) eK eF = lblVal (F := F) (eK.chal chalGammaW) cells (r.s, r.f, r.e) := by
  unfold curL
  rw [evalMQ_rlcKey kind chalGammaW eK eF _ hcol]
  simp [labelCols, hS, hF, hE, hd, lblVal, hl, rlcL, hn_s, hn_f, hn_e]

theorem sumM_eval (l : List (MixedExpr ℚ)) :
    evalMQ (sumM l) eK eF = (l.map fun g => evalMQ g eK eF).sum := evalMQ_sumM l eK eF

theorem childSum_honest (hk : kind = .traceCur ∨ kind = .traceNext)
    (hcol : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF = colVal cells r fst lst i)
    (st : ℕ) (hst : r.op = st) :
    evalMQ (childSum (F := ℚ) kind st) eK eF =
      (((childNouns r).zipIdx).map fun p =>
        (eK.chal chalAlphaW) ^ (p.2 + 1) * lblVal (F := F) (eK.chal chalGammaW) cells p.1).sum := by
  have hrl : ∀ (a b c : Hd), evalMQ (rlcKey (F := ℚ) kind chalGammaW 0 (hcols a b c)) eK eF =
      rlcL (eK.chal chalGammaW) 0 ([colVal cells r fst lst a.k, colVal cells r fst lst a.v,
        colVal cells r fst lst b.k, colVal cells r fst lst b.v, colVal cells r fst lst c.k,
        colVal cells r fst lst c.v].map (algebraMap F K)) := by
    intro a b c
    rw [hcols, evalMQ_rlcKey kind chalGammaW eK eF _ hcol]
    simp [hcols]
  unfold ChipH.childSum
  rw [sumM_eval]
  by_cases hst' : st ≤ 10
  · interval_cases st <;>
    simp [ChipH.children, childNouns, hst, hrl, evalMQ, List.zipIdx, lblVal, hl, rlcL,
      hS, hF, hE, hSf1, hSf2, hFh, hFt, hFth, hFtt, hFtth, hFttt, hM, hd, hn_s, hn_f, hn_e, hn_sf1, hn_sf2, hn_fh, hn_ft, hn_fth, hn_ftt, hn_m6]
  · obtain ⟨k, rfl⟩ : ∃ k, st = k + 11 := ⟨st - 11, by omega⟩
    simp [ChipH.children, childNouns, hst]

theorem sum_ite_range (o : ℕ) (ho : o ≤ 10) (R : K) :
    ((List.range 11).map fun st => if o = st then R else 0).sum = R := by
  interval_cases o <;> simp [List.range_succ]

theorem ccL_honest (hk : kind = .traceCur ∨ kind = .traceNext)
    (hcol : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF = colVal cells r fst lst i)
    (hop : r.op ≤ 10) :
    evalMQ (ccL (F := ℚ) kind) eK eF =
      (((childNouns r).zipIdx).map fun p =>
        (eK.chal chalAlphaW) ^ (p.2 + 1) * lblVal (F := F) (eK.chal chalGammaW) cells p.1).sum := by
  generalize hR : (((childNouns r).zipIdx).map fun p =>
        (eK.chal chalAlphaW) ^ (p.2 + 1) * lblVal (F := F) (eK.chal chalGammaW) cells p.1).sum = R
  have hterm : ∀ st ∈ ChipH.allStates, evalMQ (.Scale (kv (F := ℚ) kind st)
      (ChipH.childSum (F := ℚ) kind st) : MixedExpr ℚ) eK eF = if r.op = st then R else 0 := by
    intro st hst
    have hst' : st < 11 := List.mem_range.mp hst
    have hc : evalQ (kv (F := ℚ) kind st) eF = if r.op = st then 1 else 0 := by
      simp only [kv, hcol, cvOne cells r fst lst st (by omega)]
    simp only [evalMQ, hc]
    by_cases h : r.op = st
    · rw [← hR, ← childSum_honest cells r fst lst kind eK eF hk hcol st h]
      simp [h]
    · simp [h]
  unfold ccL
  rw [sumM_eval, List.map_map]
  have : ∀ g ∈ ChipH.allStates, ((fun g => evalMQ g eK eF) ∘ fun st => (MixedExpr.Scale (kv kind st) (ChipH.childSum kind st) : MixedExpr ℚ)) g = if r.op = g then R else 0 := hterm
  rw [List.map_congr_left this]
  exact sum_ite_range r.op hop R

theorem children_length (st : ℕ) (hst : r.op = st) :
    (ChipH.children st).length = (childNouns r).length := by
  by_cases hst' : st ≤ 10
  · interval_cases st <;> simp [ChipH.children, childNouns, hst]
  · obtain ⟨k, rfl⟩ : ∃ k, st = k + 11 := ⟨st - 11, by omega⟩
    simp [ChipH.children, childNouns, hst]

theorem cmL_honest (hcol : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF = colVal cells r fst lst i)
    (hop : r.op ≤ 10) :
    evalMQ (cmL (F := ℚ) kind) eK eF = (eK.chal chalAlphaW) ^ (childNouns r).length := by
  generalize hR : (eK.chal chalAlphaW) ^ (childNouns r).length = R
  have hterm : ∀ st ∈ ChipH.allStates, evalMQ (.Scale (kv (F := ℚ) kind st)
      (.Pow (.Var .challenge chalAlphaW) (ChipH.children st).length) : MixedExpr ℚ) eK eF =
      if r.op = st then R else 0 := by
    intro st hst
    have hst' : st < 11 := List.mem_range.mp hst
    have hc : evalQ (kv (F := ℚ) kind st) eF = if r.op = st then 1 else 0 := by
      simp only [kv, hcol, cvOne cells r fst lst st (by omega)]
    simp only [evalMQ, hc]
    by_cases h : r.op = st
    · rw [← hR, ← children_length r st h]
      simp [h]
    · simp [h]
  unfold cmL
  rw [sumM_eval, List.map_map]
  have : ∀ g ∈ ChipH.allStates, ((fun g => evalMQ g eK eF) ∘ fun st => (MixedExpr.Scale (kv kind st) (.Pow (.Var .challenge chalAlphaW) (ChipH.children st).length) : MixedExpr ℚ)) g = if r.op = g then R else 0 := hterm
  rw [List.map_congr_left this]
  exact sum_ite_range r.op hop R

end Honest


/-! ## 3. The tree-level link -/

section Tree

theorem zipIdx_sum_aux {α M : Type} [AddCommMonoid M] (d : α) (g : α → ℕ → M) :
    ∀ (L : List α) (k : ℕ), ((L.zipIdx k).map fun p => g p.1 p.2).sum =
      ∑ i ∈ Finset.range L.length, g (L.getD i d) (k + i) := by
  intro L
  induction L with
  | nil => intro k; simp
  | cons a L ih =>
    intro k
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, ih (k + 1), List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [show k + 1 + i = k + (i + 1) by omega]

theorem rowOfSkelH_op_le (sk : ComputeRowSkeleton) : (rowOfSkelH sk).op ≤ 10 := by
  unfold rowOfSkelH rowOfSkel
  cases sk.state <;> simp

theorem childNouns_length (sk : ComputeRowSkeleton) :
    (childNouns (rowOfSkelH sk)).length = fanoutComp sk.state := by
  unfold rowOfSkelH rowOfSkel
  cases sk.state <;> simp [childNouns, fanoutComp]


theorem rowOfSkelH_sfe (sk : ComputeRowSkeleton) :
    (rowOfSkelH sk).s = sk.subject ∧ (rowOfSkelH sk).f = sk.formula ∧
      (rowOfSkelH sk).e = sk.evaluation := by
  unfold rowOfSkelH rowOfSkel
  cases sk.state <;> simp

variable {Kg F K : Type} [Field Kg] [Field F] [Field K] [Algebra F K]

/-- The honest walk node value: the RLC of the handle label of the node's hosted row. -/
def nodeValH (γ : K) (cells : List Noun) (u : NTree (GenComputeRow Kg)) : K :=
  lblVal (F := F) γ cells ((rowOfSkelH u.label.skel).s, (rowOfSkelH u.label.skel).f,
    (rowOfSkelH u.label.skel).e)

/-- **The queue side of the child link**: the child sum the gates read (`ccL`) is the walk's `Σ_l α^l ·
chld(i, l)` at handle labels, for every node of the committed tree. -/
theorem cc_link
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow Kg)} {result : Noun}
    (h : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    {n : NTree (GenComputeRow Kg)} (hn : n ∈ bfsForest [airReorder t]) (α γ : K) (cells : List Noun) :
    ∑ l ∈ Finset.Icc 1 n.children.length, α ^ l *
        (((n.children[l - 1]?).map (nodeValH (F := F) γ cells)).getD 0) =
      (((childNouns (rowOfSkelH n.label.skel)).zipIdx).map fun p =>
        α ^ (p.2 + 1) * lblVal (F := F) γ cells p.1).sum := by
  have hfan : n.children.length = fanoutComp n.label.skel.state :=
    airReorder_inTree_fanout (fun v hv => genComputeSkeleton_inTree_fanout h v hv) n
      (inTree_of_mem_bfsForest_singleton hn)
  rw [Walk.sum_Icc_one_eq_range, zipIdx_sum_aux (.atom 0, .atom 0, .atom 0)
    (fun p k => α ^ (k + 1) * lblVal (F := F) γ cells p), childNouns_length, ← hfan]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x < n.children.length := Finset.mem_range.mp hx
  have hx3 : x < 3 := by
    have := Nock.NockVMROM.Thm54.ComputeWalkLabel.fanoutComp_le_three n.label.skel.state; omega
  have hl := child_link_nouns h hn ⟨x, hx3⟩ hx'
  simp only [Nat.add_sub_cancel, List.getElem?_eq_getElem hx', Option.map_some, Option.getD_some]
  rw [zero_add]
  simp only at hl
  unfold nodeValH
  obtain ⟨e1, e2, e3⟩ := rowOfSkelH_sfe (n.children[x]'hx').label.skel
  rw [e1, e2, e3]
  exact congrArg (fun q => α ^ (x + 1) * lblVal (F := F) γ cells q) hl

/-- The honest row at BFS index `j` (`1`-based), a dummy row past the end. -/
def rowAtW (W : List (NTree (GenComputeRow Kg))) (j : ℕ) : RowN :=
  match W[j - 1]? with
  | some n => rowOfSkelH n.label.skel
  | none => { op := 0, s := .atom 0, f := .atom 0, e := .atom 0 }

/-- **The three label reads of a BFS row** (current or next environment): the label RLC is the walk's
`cur`, the child sum is `Σ_l α^l chld(j, l)`, the count multiplier is `α^{fo j}`. -/
theorem reads_at
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow Kg)} {result : Noun}
    (h : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (cells : List Noun) (α γ : K) (j : ℕ) (hj1 : 1 ≤ j) (hjh : j ≤ (bfsForest [airReorder t]).length)
    (kind : VarKind) (hk : kind = .traceCur ∨ kind = .traceNext) (eK : Env K) (eF : Env F)
    (fst lst : F) (hα : eK.chal chalAlphaW = α) (hγ : eK.chal chalGammaW = γ)
    (hcol : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF =
      colVal cells (rowAtW (bfsForest [airReorder t]) j) fst lst i) :
    evalMQ (curL (F := ℚ) kind) eK eF =
        Walk.curCol (nodeValH (F := F) γ cells) (bfsForest [airReorder t]) j ∧
      evalMQ (ccL (F := ℚ) kind) eK eF =
        ∑ l ∈ Finset.Icc 1 (Walk.foCol (bfsForest [airReorder t]) j), α ^ l *
          Walk.chldCol (nodeValH (F := F) γ cells) (bfsForest [airReorder t]) j l ∧
      evalMQ (cmL (F := ℚ) kind) eK eF = α ^ (Walk.foCol (bfsForest [airReorder t]) j) := by
  set W := bfsForest [airReorder t] with hW
  have hlt : j - 1 < W.length := by omega
  have hget : W[j - 1]? = some W[j - 1] := List.getElem?_eq_getElem hlt
  have hmem : W[j - 1] ∈ W := List.getElem_mem hlt
  have hrow : rowAtW W j = rowOfSkelH W[j - 1].label.skel := by simp [rowAtW, hget]
  rw [hrow] at hcol
  have hfo : Walk.foCol W j = W[j - 1].children.length := by simp [Walk.foCol, hget]
  have hop := rowOfSkelH_op_le W[j - 1].label.skel
  refine ⟨?_, ?_, ?_⟩
  · rw [curL_honest cells _ fst lst kind eK eF hcol, hγ]
    simp [Walk.curCol, hget, nodeValH]
  · rw [ccL_honest cells _ fst lst kind eK eF hk hcol hop, hα, hγ, hfo, ← cc_link h hmem α γ cells]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [Walk.chldCol, hget]
  · rw [cmL_honest cells _ fst lst kind eK eF hcol hop, hα, hfo, childNouns_length]
    have hfan : W[j - 1].children.length = fanoutComp W[j - 1].label.skel.state :=
      airReorder_inTree_fanout (fun v hv => genComputeSkeleton_inTree_fanout h v hv) _
        (inTree_of_mem_bfsForest_singleton hmem)
    rw [hfan]

/-- The honest `𝕂` environment of BFS row `i` (`1`-based): the closed-form walk columns of this row (current)
and of the next row (`traceNext`), the walk coins and the claim publics (`pubIC = α`, the seed, `pubOut = 0`). -/
def walkEnvK (ln cnt acc : ℕ → K) (α γ seed : K) (i : ℕ) : Env K :=
  let kcol : ℕ → ℕ → K := fun j c =>
    if c = wLn then ln j else if c = wCnt then cnt j else if c = wAcc then acc j
    else if c = wInv then (cnt j - ln j)⁻¹ else 0
  ⟨kcol i, kcol (i + 1),
   fun c => if c = chalAlphaW then α else if c = chalGammaW then γ else 0,
   fun c => if c = pubIC then α else if c = pubSeed then seed else 0⟩

/-- The honest base environment of BFS row `i`: the hosted handle row of `i` and of `i + 1`, first / last flags. -/
def walkEnvF (W : List (NTree (GenComputeRow Kg))) (cells : List Noun) (i : ℕ) : Env F :=
  let fl : ℕ → F := fun j => if j = 1 then 1 else 0
  let ll : ℕ → F := fun j => if j = W.length then 1 else 0
  ⟨colVal cells (rowAtW W i) (fl i) (ll i), colVal cells (rowAtW W (i + 1)) (fl (i + 1)) (ll (i + 1)),
    fun _ => 0, fun _ => 0⟩

/-- **The nine compute-walk gates over handle labels hold at every honest row** (`1 ≤ i ≤ h`).  Child labels
are the child rows' own `(s, f, e)` handles through `child_link_nouns` (`childrenMatchSf` + the generator
induction `inTree_childCols`); the walk columns are the closed forms (`walkSat_closed`); the boundary
facts are the tiling and perfect completeness of the BFS walk.  Hypothesis: `h ≤ orderOf α`, the honest bad
condition of the walk coin (the queue non-emptiness gate; the same as the VCL compute family). -/
theorem walkGatesH_honest
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow Kg)} {result : Noun}
    (h : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (cells : List Noun) (α γ : K) (hord : (bfsForest [airReorder t]).length ≤ orderOf α)
    (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ (bfsForest [airReorder t]).length) :
    let W := bfsForest [airReorder t]
    let nodeV := nodeValH (F := F) γ cells (Kg := Kg)
    let cur := Walk.curCol nodeV W
    let seed := cur 1 * α
    let ln := lnClosed α
    let cnt := cntClosed (Walk.foCol W) α α
    let acc := accClosed cur (Walk.chldCol nodeV W) (Walk.foCol W) α seed α
    ∀ g ∈ (walkGates : List (MixedExpr ℚ)),
      evalMQ g (walkEnvK ln cnt acc α γ seed i) (walkEnvF (F := F) W cells i) = 0 := by
  intro W nodeV cur seed ln cnt acc
  have hpos : 1 ≤ W.length := by
    show 1 ≤ (Walk.bfsForest [airReorder t]).length
    rw [Walk.walk_tail_eq (airReorder t)]; simp
  have hw := walkSat_closed cur (Walk.chldCol nodeV W) (Walk.foCol W) α seed α hpos
  have hseed : seed = cur 1 * α := rfl
  have hacc : acc W.length = 0 :=
    Walk.walk_completeness hw hseed rfl (Walk.bfs_isFullBFT (nodeVal := nodeV) (airReorder t))
  have hv : Walk.BFSValidF 1 (Walk.foCol W) W.length :=
    Walk.foCol_BFSValidF [airReorder t] (List.cons_ne_nil _ _)
  have ht : 1 + Walk.Sf (Walk.foCol W) W.length = W.length :=
    Walk.foCol_Sf_tilingF [airReorder t] (List.cons_ne_nil _ _)
  have hlnc : ∀ k, 1 ≤ k → k ≤ W.length → ln k = α ^ k := fun k h1 h2 => Walk.ln_closed hw k h1 h2
  have hcnc : ∀ k, 1 ≤ k → k ≤ W.length → cnt k = α * α ^ Walk.Sf (Walk.foCol W) k :=
    fun k h1 h2 => Walk.count_closed hw k h1 h2
  have hcntlast : cnt W.length = ln W.length := by
    rw [hcnc _ hpos le_rfl, hlnc _ hpos le_rfl, ← pow_succ']
    exact congrArg (fun e => α ^ e) (by omega)
  have hne : ∀ j, 1 ≤ j → j < W.length → cnt j ≠ ln j := by
    intro j hj1 hj
    have hneq := (Nock.RedTeam.Batch478.honest_ratio_gate (K := K) hv ht hord).1 j hj1 hj
    rw [hcnc j hj1 hj.le, hlnc j hj1 hj.le, ← pow_succ', Nat.add_comm]
    exact hneq
  have hrd1 := reads_at (F := F) h cells α γ i hi1 hih .traceCur (Or.inl rfl)
    (walkEnvK ln cnt acc α γ seed i) (walkEnvF (F := F) W cells i)
    (if i = 1 then 1 else 0) (if i = W.length then 1 else 0)
    (by simp [walkEnvK, chalAlphaW, chalGammaW]) (by simp [walkEnvK, chalAlphaW, chalGammaW])
    (fun j => rfl)
  refine walkGates_hold hw (walkEnvK ln cnt acc α γ seed i) (walkEnvF (F := F) W cells i) i hi1 hih
    (by simp [walkEnvK, chalAlphaW]) (by simp [walkEnvK, pubIC])
    (by simp [walkEnvK, pubSeed, pubIC])
    (by simp [walkEnvK, wLn] <;> rfl) (by simp [walkEnvK, wLn] <;> rfl) (by simp [walkEnvK, wLn, wCnt] <;> rfl)
    (by simp [walkEnvK, wLn, wCnt] <;> rfl) (by simp [walkEnvK, wLn, wCnt, wAcc] <;> rfl)
    (by simp [walkEnvK, wLn, wCnt, wAcc] <;> rfl) ?_ (by simp [walkEnvF, firstCol])
    (by simp [walkEnvF, lastCol]) (by simp [walkEnvK, pubOut, pubIC, pubSeed] <;> exact hacc.symm) hcntlast ?_
  · intro hlt
    simp only [walkEnvK, wLn, wCnt, wAcc, wInv]
    simp only [show (67 : ℕ) ≠ 58 by decide, show (67 : ℕ) ≠ 61 by decide, show (67 : ℕ) ≠ 64 by decide,
      if_false, if_true]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (hne i hi1 hlt))
  · refine ⟨hrd1.1, hrd1.2.1, hrd1.2.2, fun hlt => ?_⟩
    exact reads_at (F := F) h cells α γ (i + 1) (by omega) hlt .traceNext (Or.inr rfl)
      (walkEnvK ln cnt acc α γ seed i) (walkEnvF (F := F) W cells i)
      (if i + 1 = 1 then 1 else 0) (if i + 1 = W.length then 1 else 0)
      (by simp [walkEnvK, chalAlphaW, chalGammaW]) (by simp [walkEnvK, chalAlphaW, chalGammaW])
      (fun j => rfl)


end Tree

end

end Nock.NockVMROM.Thm54.VclL.Handle
