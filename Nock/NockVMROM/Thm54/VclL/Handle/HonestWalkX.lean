/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestWalkX.lean

  **The nine walk gates of `computeChipVCLHX`
  (cols `111..122`) at every honest BFS row of a generated `NTree SkelX` tree.**

  * `walkGatesX_hold` — the nine `𝕂` gates vanish on a row whose columns are a `Walk.WalkSat` walk.
  * `hlX`, `lblX`, `childNounsX` — honest handle labels; the child triples a row reads (the `s10L` child
    is `(s, atom (a / 2), e)`, read through `labAtom` with the constant-zero kind).
  * `curLX_honest`, `childSumX_honest`, `ccLX_honest`, `cmLX_honest` — the label reads at `colX`.
  * `ChildLinkX`, `genX_childLink`, `chain_childLink`, `childLink_of_genX` — every node's children
    carry, in order, the triples its row reads (by the generator; chain levels by `genChainF`).
  * `cc_linkX`, `reads_atX`, **`walkGatesX_honest`** — every walk gate at every BFS row `1 ≤ i ≤ |W|`,
    at the closed-form walk `walkEnvKX / walkEnvFX`, under `HdlOK`, `SmallX` and `|W| ≤ orderOf α`.

  NOT here: the congruence to the real chip environment (the twin of `walk_gates_real`), which needs
  the trace `compTraceX` of step 3.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
import Nock.NockVMROM.Thm54.VclL.Handle.WalkGatesH
import Nock.NockVMROM.Thm54.VclL.Handle.HonestRowX

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX

open Nock Nock.Reified Module
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle (evalQ_notC evalQ_cc)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (chalAlphaW chalGammaW pubIC pubSeed pubOut cc notC wv kv sumM)
open Nock.NockVMROM.Thm54.VclL.Handle (rlcL)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestRowX (SmallX)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX (stIdx)
open Nock.Edit Nock.Edit.GenX Nock.Walk Nock.Jet Nock.Noun
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL (hdN tlN)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX

noncomputable section

section Gates
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **What a row of the J-8 walk reads**: the current row's label, child sum and count multiplier;
the next row's, when there is one. -/
structure RowReadsX (eK : Env K) (eF : Env F) (cur ccC cmC : K) (hasNext : Prop) (curN ccN cmN : K) :
    Prop where
  curC : evalMQ (curLX (F := ℚ) .traceCur) eK eF = cur
  ccC : evalMQ (ccLX (F := ℚ) .traceCur) eK eF = ccC
  cmC : evalMQ (cmLX (F := ℚ) .traceCur) eK eF = cmC
  nxt : hasNext → evalMQ (curLX (F := ℚ) .traceNext) eK eF = curN ∧
    evalMQ (ccLX (F := ℚ) .traceNext) eK eF = ccN ∧ evalMQ (cmLX (F := ℚ) .traceNext) eK eF = cmN

/-- **The nine walk gates of `computeChipVCLHX` vanish on a row whose columns are a `WalkSat` walk**
(row `i`, `1`-based, of `h`; the twin of `walkGates_hold`). -/
theorem walkGatesX_hold {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {ln cnt acc : ℕ → K}
    {α seed : K} {h : ℕ}
    (hw : Walk.WalkSat cur chld' fo ln cnt acc α seed α h)
    (eK : Env K) (eF : Env F) (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ h)
    (hα : eK.chal chalAlphaW = α) (hIC : eK.pub pubIC = α) (hseed : eK.pub pubSeed = seed)
    (hlnC : eK.trace wLnX = ln i) (hlnN : eK.traceNext wLnX = ln (i + 1))
    (hcnC : eK.trace wCntX = cnt i) (hcnN : eK.traceNext wCntX = cnt (i + 1))
    (hacC : eK.trace wAccX = acc i) (hacN : eK.traceNext wAccX = acc (i + 1))
    (hinv : i < h → eK.trace wInvX * (cnt i - ln i) = 1)
    (hfirst : eF.trace firstX = if i = 1 then 1 else 0)
    (hlast : eF.trace lastX = if i = h then 1 else 0)
    (hout : eK.pub pubOut = acc h) (hcntlast : cnt h = ln h)
    (hrd : RowReadsX eK eF (cur i) (∑ l ∈ Finset.Icc 1 (fo i), α ^ l * chld' i l) (α ^ fo i)
      (i < h) (cur (i + 1)) (∑ l ∈ Finset.Icc 1 (fo (i + 1)), α ^ l * chld' (i + 1) l)
      (α ^ fo (i + 1))) :
    ∀ g ∈ (walkGatesX : List (MixedExpr ℚ)), evalMQ g eK eF = 0 := by
  intro g hg
  have hnl : algebraMap F K (evalQ (notC (F := ℚ) lastX) eF) = if i = h then 0 else 1 := by
    simp only [evalQ_notC, hlast]; split <;> simp
  have hfl : algebraMap F K (evalQ (cc (F := ℚ) firstX) eF) = if i = 1 then 1 else 0 := by
    simp only [evalQ_cc, hfirst]; split <;> simp
  have hll : algebraMap F K (evalQ (cc (F := ℚ) lastX) eF) = if i = h then 1 else 0 := by
    simp only [evalQ_cc, hlast]; split <;> simp
  simp only [walkGatesX, List.mem_cons, List.not_mem_nil, or_false] at hg
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
      simp only [evalMQ, ChipH.wv, hih', if_false, one_mul, hlnN, hacN, hacC, hcnC,
        (hrd.nxt (by omega)).1, (hrd.nxt (by omega)).2.1]
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

/-! ## 2. The honest label reads -/

section Reads
variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))

/-- The six label values `(k, v)` of a noun triple, as honest handles. -/
def hlX (t : Noun × Noun × Noun) : List F :=
  [hk H t.1, hv H t.1, hk H t.2.1, hv H t.2.1, hk H t.2.2, hv H t.2.2]

/-- **The honest walk label value** of a noun triple: the RLC of its handles at the coin `γ`. -/
def lblX (γ : K) (t : Noun × Noun × Noun) : K := rlcL γ 0 ((hlX (F := F) H t).map (algebraMap F K))

/-- **The child triples of a noun row** in `childrenX` order (`s10L`: the level `a / 2` as an atom). -/
def childNounsX (r : RowNX) : List (Noun × Noun × Noun) :=
  match r.st with
  | .s2 => [(r.s, r.fth, r.sf1), (r.s, r.ftt, r.sf2), (r.sf1, r.sf2, r.e)]
  | .s3 => [(r.s, r.ft, r.sf1)]
  | .s4 => [(r.s, r.ft, r.sf1)]
  | .s5 => [(r.s, r.fth, r.sf1), (r.s, r.ftt, r.sf2)]
  | .s6 => [(r.s, r.m, r.sf1), (r.s, r.fth, r.sf2)]
  | .s7 => [(r.sf2, r.ftt, r.sf1), (r.s, r.fth, r.sf2)]
  | .s8 => [(r.m, r.ftt, r.sf1), (r.s, r.fth, r.sf2)]
  | .s9 => [(r.s, r.ftt, r.sf1), (r.sf1, r.m, r.sf2)]
  | .cons => [(r.s, r.fh, r.sf1), (r.s, r.ft, r.sf2)]
  | .s10 => [(r.s, r.fttt, r.sf1), (r.s, r.ftt, r.sf2), (r.sf2, r.ftth, r.e)]
  | .s10L => [(r.s, .atom (chainAxis r.f / 2), r.e)]
  | .s11s => [(r.s, r.ftt, r.e)]
  | .s11d => [(r.s, r.fttt, r.sf1), (r.s, r.ftt, r.e)]
  | .s11j => [(r.s, r.fttt, r.sf1)]
  | _ => []

theorem childrenX_length_eq (r : RowNX) : (childrenX (stIdx r.st)).length = (childNounsX r).length := by
  unfold childNounsX; cases r.st <;> rfl

variable (kind : VarKind) (eK : Env K) (eF : Env F) (vals : ℕ → F)

/-- A label key with `none` entries evaluates to `rlcL` of its values (`none` ↦ `0`). -/
theorem evalMQ_rlcKeyL (γ : ℕ) (hv : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF = vals i) :
    ∀ (n : ℕ) (l : List (Option ℕ)), evalMQ (rlcKeyL (F := ℚ) kind γ n l) eK eF =
      rlcL (eK.chal γ) n (l.map fun o => algebraMap F K (o.elim 0 vals)) := by
  intro n l
  induction l generalizing n with
  | nil => simp [rlcKeyL, evalMQ, rlcL]
  | cons o l ih =>
    cases o with
    | none => simp [rlcKeyL, rlcL, ih]
    | some i => simp only [rlcKeyL, evalMQ, rlcL, List.map_cons, ih, hv, Option.elim]

variable {H pd} {r : RowNX} {fst lst : F}

theorem curLX_honest (hcol : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF = colX H pd r fst lst i) :
    evalMQ (curLX (F := ℚ) kind) eK eF = lblX (F := F) H (eK.chal chalGammaW) (r.s, r.f, r.e) := by
  unfold curLX
  rw [evalMQ_rlcKeyL kind eK eF _ chalGammaW hcol]
  simp [labelColsX, labX, xS, xF, xE, hdX, lblX, hlX, colX, hN]

theorem childSumX_honest
    (hcol : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF = colX H pd r fst lst i)
    (hAt : r.st = .s10L → hk (F := F) H (.atom (chainAxis r.f / 2)) = 0 ∧
      hv (F := F) H (.atom (chainAxis r.f / 2)) = ((chainAxis r.f / 2 : ℕ) : F)) :
    evalMQ (childSumX (F := ℚ) kind (stIdx r.st)) eK eF =
      (((childNounsX r).zipIdx).map fun q =>
        (eK.chal chalAlphaW) ^ (q.2 + 1) * lblX (F := F) H (eK.chal chalGammaW) q.1).sum := by
  have hrl : ∀ l : List (Option ℕ), evalMQ (rlcKeyL (F := ℚ) kind chalGammaW 0 l) eK eF =
      rlcL (eK.chal chalGammaW) 0 (l.map fun o => algebraMap F K (o.elim 0 (colX H pd r fst lst))) :=
    fun l => evalMQ_rlcKeyL kind eK eF _ chalGammaW hcol 0 l
  unfold childSumX
  rw [Nock.NockVMROM.Thm54.VclL.Handle.evalMQ_sumM]
  cases hst : r.st <;>
    simp [childrenX, childNounsX, hst, stIdx, hrl, evalMQ, List.zipIdx, lblX, hlX, labX, labAtom,
      xS, xF, xE, xSf1, xSf2, xFh, xFt, xFth, xFtt, xFtth, xFttt, xM, hdX, colX, hN, cV, vX]
  all_goals (obtain ⟨h1, h2⟩ := hAt hst; simp [h1, h2, map_natCast])

theorem sum_onehot17 (st : StateX) (R : K) :
    ((List.range nStates).map fun j => if stIdx st = j then R else 0).sum = R := by
  cases st <;> simp [List.range_succ, nStates, stIdx]

theorem ccLX_honest
    (hcol : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF = colX H pd r fst lst i)
    (hAt : r.st = .s10L → hk (F := F) H (.atom (chainAxis r.f / 2)) = 0 ∧
      hv (F := F) H (.atom (chainAxis r.f / 2)) = ((chainAxis r.f / 2 : ℕ) : F)) :
    evalMQ (ccLX (F := ℚ) kind) eK eF =
      (((childNounsX r).zipIdx).map fun q =>
        (eK.chal chalAlphaW) ^ (q.2 + 1) * lblX (F := F) H (eK.chal chalGammaW) q.1).sum := by
  generalize hR : (((childNounsX r).zipIdx).map fun q =>
        (eK.chal chalAlphaW) ^ (q.2 + 1) * lblX (F := F) H (eK.chal chalGammaW) q.1).sum = R
  have hterm : ∀ j ∈ allStatesX, evalMQ (.Scale (kv (F := ℚ) kind j)
      (childSumX (F := ℚ) kind j) : MixedExpr ℚ) eK eF = if stIdx r.st = j then R else 0 := by
    intro j hj
    have hj' : j < 17 := List.mem_range.mp hj
    have hc : evalQ (kv (F := ℚ) kind j) eF = if stIdx r.st = j then 1 else 0 := by
      simp only [kv, hcol, colX_st H pd r fst lst j hj']
    simp only [evalMQ, hc]
    by_cases h : stIdx r.st = j
    · subst h; rw [← hR, ← childSumX_honest kind eK eF hcol hAt]; simp
    · simp [h]
  unfold ccLX
  rw [Nock.NockVMROM.Thm54.VclL.Handle.evalMQ_sumM, List.map_map]
  have : ∀ g ∈ allStatesX, ((fun g => evalMQ g eK eF) ∘ fun st =>
      (MixedExpr.Scale (kv kind st) (childSumX kind st) : MixedExpr ℚ)) g =
      if stIdx r.st = g then R else 0 := hterm
  rw [List.map_congr_left this]
  exact sum_onehot17 r.st R

theorem cmLX_honest (hcol : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF = colX H pd r fst lst i) :
    evalMQ (cmLX (F := ℚ) kind) eK eF = (eK.chal chalAlphaW) ^ (childNounsX r).length := by
  generalize hR : (eK.chal chalAlphaW) ^ (childNounsX r).length = R
  have hterm : ∀ j ∈ allStatesX, evalMQ (.Scale (kv (F := ℚ) kind j)
      (.Pow (.Var .challenge chalAlphaW) (childrenX j).length) : MixedExpr ℚ) eK eF =
      if stIdx r.st = j then R else 0 := by
    intro j hj
    have hj' : j < 17 := List.mem_range.mp hj
    have hc : evalQ (kv (F := ℚ) kind j) eF = if stIdx r.st = j then 1 else 0 := by
      simp only [kv, hcol, colX_st H pd r fst lst j hj']
    simp only [evalMQ, hc]
    by_cases h : stIdx r.st = j
    · subst h; rw [← hR, ← childrenX_length_eq r]; simp
    · simp [h]
  unfold cmLX
  rw [Nock.NockVMROM.Thm54.VclL.Handle.evalMQ_sumM, List.map_map]
  have : ∀ g ∈ allStatesX, ((fun g => evalMQ g eK eF) ∘ fun st =>
      (MixedExpr.Scale (kv kind st) (.Pow (.Var .challenge chalAlphaW) (childrenX st).length) :
        MixedExpr ℚ)) g = if stIdx r.st = g then R else 0 := hterm
  rw [List.map_congr_left this]
  exact sum_onehot17 r.st R

end Reads

/-! ## 3. The child link of a generated tree -/

section Link

/-- The `(s, f, e)` triple of a node. -/
def tripOf (u : NTree SkelX) : Noun × Noun × Noun :=
  (u.label.subject, u.label.formula, u.label.evaluation)

/-- **The child link**: a node's children carry, in order, the child triples its row reads. -/
def ChildLinkX (u : NTree SkelX) : Prop := u.children.map tripOf = childNounsX (rowOfSkelX u.label)

set_option hygiene false in
macro "fin_link" : tactic => `(tactic| (
  simp only [ChildLinkX, mkX_children, mkX_label, rowOfSkelX, childNounsX, kidE, kidF, SkelX.row,
    List.map_cons, List.map_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some,
    Option.getD_some, tripOf]
  try simp_all [hdN, tlN, genChain, genChainF_label]))

theorem genX_childLink {R : Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) : ChildLinkX t := by
  induction n, s, f using genComputeSkeletonX.induct R generalizing t r
  all_goals first | (simp_all [genComputeSkeletonX]; done) | skip
  case case3 n s b c d tl l tr r' hd hbc ih1 ih2 =>
    simp only [genComputeSkeletonX, hd, hbc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    gen_cells
    fin_link
  case case5 n s ax r' hs' =>
    simp only [genComputeSkeletonX, hs', Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    gen_cells
    fin_link
  case case7 n s u =>
    simp only [genComputeSkeletonX, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    gen_cells
    fin_link
  case case8 n s b c tl l tr r1 hc hb t2 r2 hm ih1 ih2 ih3 =>
    simp only [genComputeSkeletonX, hb, hc, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    gen_cells
    fin_link
  case case11 n s u t2 v hx ih =>
    simp only [genComputeSkeletonX, hx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    gen_cells
    fin_link
  case case13 n s u t0 v hx ih =>
    simp only [genComputeSkeletonX, hx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    gen_cells
    fin_link
  case case15 n s b c tl l tr r1 hc hb ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    gen_cells
    fin_link
  case case17 n s b c d tC hb t2 r1 hc ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    gen_cells
    fin_link
  case case19 n s b c d tC hb t2 r1 hc ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    gen_cells
    fin_link
  case case22 n s b c t1 r1 hb t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    gen_cells
    fin_link
  case case25 n s b c t1 r1 hb t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    gen_cells
    fin_link
  case case28 n s ax c t1 core hc arm harm t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hc, harm, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    gen_cells
    fin_link
  case case32 n s ax c d tl new tr old hd hc e he ih1 ih2 =>
    simp only [genComputeSkeletonX, hc, hd, he, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    gen_cells
    fin_link
  case case35 n s b clue body t1 v hcl r1 hj ih1 =>
    simp only [genComputeSkeletonX, hcl, hj, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    gen_cells
    fin_link
  case case36 n s b clue body t1 v hcl hj t2 r1 hB ih1 ih2 =>
    simp only [genComputeSkeletonX, hcl, hj, hB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    gen_cells
    fin_link
  case case39 n s b body t2 r1 hB ih1 =>
    simp only [genComputeSkeletonX, hB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    gen_cells
    fin_link
theorem chain_childLink {u : NTree SkelX} (hu : ChainNode u) : ChildLinkX u := by
  obtain ⟨old, e, k, a, rfl, hc, h1, h2⟩ := hu
  cases k with
  | zero => simp [ChildLinkX, genChainF, rowOfSkelX, childNounsX]
  | succ k =>
    by_cases ha : 2 ≤ a
    · obtain ⟨l1, l2, l3, -⟩ := genChainF_label old e k (a / 2)
      simp [ChildLinkX, genChainF, ha, rowOfSkelX, childNounsX, tripOf, chainAxis, l1, l2, l3]
    · simp [ChildLinkX, genChainF, ha, rowOfSkelX, childNounsX]

/-- **Every node of a generated tree satisfies the child link.** -/
theorem childLink_of_genX {R : Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) {u : NTree SkelX} (hu : InTree t u) : ChildLinkX u := by
  rcases genX_inTree h hu with ⟨m, hm⟩ | hc
  · exact genX_childLink hm
  · exact chain_childLink hc

/-- A row's `(s, f, e)` is its node's triple. -/
theorem rowOfSkelX_trip (sk : SkelX) :
    ((rowOfSkelX sk).s, (rowOfSkelX sk).f, (rowOfSkelX sk).e) =
      (sk.subject, sk.formula, sk.evaluation) := by
  unfold rowOfSkelX; cases sk.state <;> rfl

end Link

/-! ## 4. The walk over the BFS of a generated tree -/

section Tree
variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))

/-- The honest walk node value: the label RLC of the node's `(s, f, e)`. -/
def nodeValX (γ : K) (u : NTree SkelX) : K := lblX (F := F) H γ (tripOf u)

/-- The honest noun row at BFS index `j` (`1`-based), a dummy `s10T` row past the end. -/
def rowAtWX (W : List (NTree SkelX)) (j : ℕ) : RowNX :=
  match W[j - 1]? with
  | some n => rowOfSkelX n.label
  | none => { st := .s10T, s := .atom 0, f := .atom 1, e := .atom 0 }

variable {H}

theorem hAt_of_small {p : ℕ} (hH : HdlOK p H) (hp : 0 < p) {r : RowNX} (hs : SmallX p r) :
    r.st = .s10L → hk (F := F) H (.atom (chainAxis r.f / 2)) = 0 ∧
      hv (F := F) H (.atom (chainAxis r.f / 2)) = ((chainAxis r.f / 2 : ℕ) : F) := by
  intro hst
  have hlt : chainAxis r.f / 2 < p := by
    simp only [SmallX, hst] at hs
    cases hf : r.f with
    | atom a => have := hs a hf; simp only [chainAxis]; omega
    | cell _ _ => simp [chainAxis, hp]
  rw [hk, hv, hH.small _ hlt]; simp

/-- **The queue side of the child link** at honest labels. -/
theorem cc_linkX {R : Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) {u : NTree SkelX} (hu : u ∈ bfsForest [t]) (α γ : K) :
    ∑ l ∈ Finset.Icc 1 u.children.length, α ^ l *
        (((u.children[l - 1]?).map (nodeValX (F := F) H γ)).getD 0) =
      (((childNounsX (rowOfSkelX u.label)).zipIdx).map fun q =>
        α ^ (q.2 + 1) * lblX (F := F) H γ q.1).sum := by
  have hl : u.children.map tripOf = childNounsX (rowOfSkelX u.label) :=
    childLink_of_genX h (Nock.NockVMROM.Thm54.TraceGen.inTree_of_mem_bfsForest_singleton hu)
  rw [← hl, Walk.sum_Icc_one_eq_range,
    Nock.NockVMROM.Thm54.VclL.Handle.zipIdx_sum_aux (.atom 0, .atom 0, .atom 0)
      (fun q k => α ^ (k + 1) * lblX (F := F) H γ q), List.length_map]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x < u.children.length := Finset.mem_range.mp hx
  simp [List.getElem?_eq_getElem hx', nodeValX, hx']

/-- **The three label reads of a BFS row** of a generated tree (current or next environment). -/
theorem reads_atX {R : Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) (hH : HdlOK (ringChar F) H) (hp : 0 < ringChar F)
    (hsm : ∀ u, InTree t u → SmallX (ringChar F) (rowOfSkelX u.label))
    (α γ : K) (j : ℕ) (hj1 : 1 ≤ j) (hjh : j ≤ (bfsForest [t]).length)
    (kind : VarKind) (eK : Env K) (eF : Env F)
    (fst lst : F) (hα : eK.chal chalAlphaW = α) (hγ : eK.chal chalGammaW = γ)
    (hcol : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF =
      colX H pd (rowAtWX (bfsForest [t]) j) fst lst i) :
    evalMQ (curLX (F := ℚ) kind) eK eF = Walk.curCol (nodeValX (F := F) H γ) (bfsForest [t]) j ∧
      evalMQ (ccLX (F := ℚ) kind) eK eF =
        ∑ l ∈ Finset.Icc 1 (Walk.foCol (bfsForest [t]) j), α ^ l *
          Walk.chldCol (nodeValX (F := F) H γ) (bfsForest [t]) j l ∧
      evalMQ (cmLX (F := ℚ) kind) eK eF = α ^ (Walk.foCol (bfsForest [t]) j) := by
  set W := bfsForest [t] with hW
  have hlt : j - 1 < W.length := by omega
  have hget : W[j - 1]? = some W[j - 1] := List.getElem?_eq_getElem hlt
  have hmem : W[j - 1] ∈ W := List.getElem_mem hlt
  have hin : InTree t W[j - 1] := Nock.NockVMROM.Thm54.TraceGen.inTree_of_mem_bfsForest_singleton hmem
  have hrow : rowAtWX W j = rowOfSkelX W[j - 1].label := by simp [rowAtWX, hget]
  rw [hrow] at hcol
  have hAt := hAt_of_small (F := F) hH hp (hsm _ hin)
  have hfo : Walk.foCol W j = W[j - 1].children.length := by simp [Walk.foCol, hget]
  have hl : W[j - 1].children.map tripOf = childNounsX (rowOfSkelX W[j - 1].label) :=
    childLink_of_genX h hin
  refine ⟨?_, ?_, ?_⟩
  · rw [curLX_honest kind eK eF hcol, hγ, rowOfSkelX_trip]
    simp [Walk.curCol, hget, nodeValX, tripOf]
  · rw [ccLX_honest kind eK eF hcol hAt, hα, hγ, hfo, ← cc_linkX h hmem α γ]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [Walk.chldCol, hget]
  · rw [cmLX_honest kind eK eF hcol, hα, hfo, ← hl, List.length_map]

/-- The honest `𝕂` environment of BFS row `i` (the closed-form walk columns at `111..122`). -/
def walkEnvKX (ln cnt acc : ℕ → K) (α γ seed : K) (i : ℕ) : Env K :=
  let kcol : ℕ → ℕ → K := fun j c =>
    if c = wLnX then ln j else if c = wCntX then cnt j else if c = wAccX then acc j
    else if c = wInvX then (cnt j - ln j)⁻¹ else 0
  ⟨kcol i, kcol (i + 1),
   fun c => if c = chalAlphaW then α else if c = chalGammaW then γ else 0,
   fun c => if c = pubIC then α else if c = pubSeed then seed else 0⟩

/-- The honest base environment of BFS row `i`: `colX` of rows `i` and `i + 1`, first / last flags. -/
def walkEnvFX (W : List (NTree SkelX)) (i : ℕ) : Env F :=
  let fl : ℕ → F := fun j => if j = 1 then 1 else 0
  let ll : ℕ → F := fun j => if j = W.length then 1 else 0
  ⟨colX H pd (rowAtWX W i) (fl i) (ll i), colX H pd (rowAtWX W (i + 1)) (fl (i + 1)) (ll (i + 1)),
    fun _ => 0, fun _ => 0⟩

/-- **The nine walk gates of `computeChipVCLHX` hold at every honest BFS row** of a generated tree
(`1 ≤ i ≤ |W|`), at the closed-form walk. -/
theorem walkGatesX_honest {R : Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) (hH : HdlOK (ringChar F) H) (hp : 0 < ringChar F)
    (hsm : ∀ u, InTree t u → SmallX (ringChar F) (rowOfSkelX u.label))
    (α γ : K) (hord : (bfsForest [t]).length ≤ orderOf α)
    (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ (bfsForest [t]).length) :
    let W := bfsForest [t]
    let nodeV := nodeValX (F := F) H γ
    let cur := Walk.curCol nodeV W
    let seed := cur 1 * α
    let ln := lnClosed α
    let cnt := cntClosed (Walk.foCol W) α α
    let acc := accClosed cur (Walk.chldCol nodeV W) (Walk.foCol W) α seed α
    ∀ g ∈ (walkGatesX : List (MixedExpr ℚ)),
      evalMQ g (walkEnvKX ln cnt acc α γ seed i) (walkEnvFX (F := F) (H := H) pd W i) = 0 := by
  intro W nodeV cur seed ln cnt acc
  have hpos : 1 ≤ W.length := by
    show 1 ≤ (Walk.bfsForest [t]).length
    rw [Walk.walk_tail_eq t]; simp
  have hw := walkSat_closed cur (Walk.chldCol nodeV W) (Walk.foCol W) α seed α hpos
  have hseed : seed = cur 1 * α := rfl
  have hacc : acc W.length = 0 :=
    Walk.walk_completeness hw hseed rfl (Walk.bfs_isFullBFT (nodeVal := nodeV) t)
  have hv : Walk.BFSValidF 1 (Walk.foCol W) W.length :=
    Walk.foCol_BFSValidF [t] (List.cons_ne_nil _ _)
  have ht : 1 + Walk.Sf (Walk.foCol W) W.length = W.length :=
    Walk.foCol_Sf_tilingF [t] (List.cons_ne_nil _ _)
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
  have hrd1 := reads_atX (F := F) pd h hH hp hsm α γ i hi1 hih .traceCur
    (walkEnvKX ln cnt acc α γ seed i) (walkEnvFX (F := F) (H := H) pd W i)
    (if i = 1 then 1 else 0) (if i = W.length then 1 else 0)
    (by simp [walkEnvKX, chalAlphaW, chalGammaW]) (by simp [walkEnvKX, chalAlphaW, chalGammaW])
    (fun j => rfl)
  refine walkGatesX_hold hw (walkEnvKX ln cnt acc α γ seed i) (walkEnvFX (F := F) (H := H) pd W i) i hi1 hih
    (by simp [walkEnvKX, chalAlphaW]) (by simp [walkEnvKX, pubIC])
    (by simp [walkEnvKX, pubSeed, pubIC])
    (by simp [walkEnvKX, wLnX] <;> rfl) (by simp [walkEnvKX, wLnX] <;> rfl)
    (by simp [walkEnvKX, wLnX, wCntX] <;> rfl) (by simp [walkEnvKX, wLnX, wCntX] <;> rfl)
    (by simp [walkEnvKX, wLnX, wCntX, wAccX] <;> rfl) (by simp [walkEnvKX, wLnX, wCntX, wAccX] <;> rfl)
    ?_ (by simp [walkEnvFX, colX, firstX]) (by simp [walkEnvFX, colX, lastX])
    (by simp [walkEnvKX, pubOut, pubIC, pubSeed] <;> exact hacc.symm) hcntlast ?_
  · intro hlt
    simp only [walkEnvKX, wLnX, wCntX, wAccX, wInvX]
    simp only [show (120 : ℕ) ≠ 111 by decide, show (120 : ℕ) ≠ 114 by decide,
      show (120 : ℕ) ≠ 117 by decide, if_false, if_true]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (hne i hi1 hlt))
  · refine ⟨hrd1.1, hrd1.2.1, hrd1.2.2, fun hlt => ?_⟩
    exact reads_atX (F := F) pd h hH hp hsm α γ (i + 1) (by omega) hlt .traceNext
      (walkEnvKX ln cnt acc α γ seed i) (walkEnvFX (F := F) (H := H) pd W i)
      (if i + 1 = 1 then 1 else 0) (if i + 1 = W.length then 1 else 0)
      (by simp [walkEnvKX, chalAlphaW, chalGammaW]) (by simp [walkEnvKX, chalAlphaW, chalGammaW])
      (fun j => rfl)

end Tree

end

end Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX
