/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AReadsAt.lean

* `labV`, `sIdx9`, `nodeLab9`, **`nodeV9`** — the honest walk node value: the RLC at `γ` of the node's label
    `(s.k, s.v, f.k, f.v, e.k, e.v)` read through `colX9` (the formula handle of an `s10S` node is its routed
    handle `(2, id)` / `(3, 64·id + m)`, columns 27 / 28).
  * `ChildLink9 u` — the row of `u` reads, child slot by child slot (`childrenX9` of its chip state), exactly
    its children's labels.
  * `curLX9_read`, `ccLX9_read`, `cmLX9_read`, **`readsAt9_of_link`** — on any BFS list whose nodes all satisfy
    the child link, `ReadsAt9` holds at `nodeV9`.
  * `s10_kids`, `link_old`, `link_chain`, `link_seg`, `link_s10B`, `link_gen`, **`link_all`** — every node of
    `genX9T t` of a generated run satisfies the child link (per `Node9` class: old / `s0B` rows by J-8's link,
    `s10B` by the segment root's routed handle, `s10S` by the next segment's handle or the closing `(0, 1)`).
  * **`readsAt9_honest`** (generic `F`) / **`readsAt9_honest_zmod`** (`F = ZMod p`, `idOf = idOf9 …`): the
    `hrd` of `HonestSatX9.computeChipVCLHX9_honest_sat` at `t9 = genX9T t`, `nodeV = nodeV9 … γ`.
    Hypotheses: `HdlOK p H`; `2^62 ≤ p` (the `s10L` atom child `a/2 < 2^61` and the `atom 1` closing handle are
    small); `p ≤ 2^64` (a field `s10B` axis has `top n = 1`, matching `vLab = 64·id + 1`); for the generic form,
    `idOf n = (H (atom n)).2` on big axes (`idOf9_big`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.HonestWalkX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AReads
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AChains

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReadsAt

open Nock Nock.Reified Nock.Walk Nock.Framework
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle (evalMQ evalQ rlcL)
open Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (chalAlphaW chalGammaW kv)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX (stIdx stIdx_lt)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen
open Nock.NockVMROM.Thm54 (mapNTree_children)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow (colX9 colS0B colS10B colS10S)
open Nock.NockVMROM.Thm54.VclL.HonestWalkX9 (ReadsAt9 rowAt9 fl1 llW)
open Nock.J9A.NounAx (top segAx segRd)

noncomputable section

/-! ## 1. The honest node value and the child link -/

section Defs
variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)

/-- The values of a label key at a column vector (`none` ↦ `0`). -/
def labV (col : ℕ → F) (L : List (Option ℕ)) : List F := L.map fun o => o.elim 0 col

/-- The one-hot chip-state column of a J-9 A row. -/
def sIdx9 (l : LX9) : ℕ :=
  match l.chip with
  | .old => stIdx l.rn.st
  | .s0B => 123
  | .s10B => 124
  | .s10S => 125

/-- **The honest label of a node**: its six label handles, read through `colX9`. -/
def nodeLab9 (u : NTree LX9) : List F := labV (colX9 H pd idOf u.label 0 0) labelColsX

/-- **The honest walk node value**: the RLC at `γ` of the node's label (twin of `HonestWalkX.nodeValX`). -/
def nodeV9 (γ : K) (u : NTree LX9) : K := rlcL γ 0 ((nodeLab9 (F := F) H pd idOf u).map (algebraMap F K))

/-- **The child link**: the child-slot label reads of `u`'s row are, in order, its children's labels. -/
def ChildLink9 (u : NTree LX9) : Prop :=
  (childrenX9 (sIdx9 u.label)).map (labV (colX9 (F := F) H pd idOf u.label 0 0)) =
    u.children.map (nodeLab9 (F := F) H pd idOf)

end Defs

/-! ## 2. Column facts -/

section Cols
variable {F : Type} [Field F]
variable (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)

/-- The flags only sit at columns 17 / 18. -/
theorem colX9_fl (l : LX9) (fst lst : F) (c : ℕ) (h17 : c ≠ 17) (h18 : c ≠ 18) :
    colX9 H pd idOf l fst lst c = colX9 H pd idOf l 0 0 c := by
  rcases l with ⟨row, chip, n, m, rn⟩
  cases chip <;> simp [colX9, colX, colS0B, colS10B, colS10S, h17, h18]

/-- A label key reads only columns `≥ 19`. -/
def okKey (L : List (Option ℕ)) : Bool := L.all fun o => o.all fun c => decide (19 ≤ c)

/-- Every label key column of a walk read sits at `≥ 19`. -/
theorem keys_ge19 : (statesX9.all fun j => (childrenX9 j).all okKey) = true := by decide +kernel

theorem labelCols_ge19 : okKey labelColsX = true := by decide +kernel

theorem okKey_of_mem {j : ℕ} (hj : j ∈ statesX9) {L : List (Option ℕ)} (hL : L ∈ childrenX9 j) : okKey L = true :=
  List.all_eq_true.mp (List.all_eq_true.mp keys_ge19 j hj) L hL

theorem labV_fl (l : LX9) (fst lst : F) (L : List (Option ℕ)) (hL : okKey L = true) :
    labV (colX9 H pd idOf l fst lst) L = labV (colX9 H pd idOf l 0 0) L := by
  unfold labV
  refine List.map_congr_left fun o ho => ?_
  cases o with
  | none => rfl
  | some c =>
    have := List.all_eq_true.mp hL _ ho
    simp only [Option.all, decide_eq_true_eq] at this
    simp only [Option.elim]
    exact colX9_fl H pd idOf l fst lst c (by omega) (by omega)

theorem sIdx9_mem (l : LX9) : sIdx9 l ∈ statesX9 := by
  rcases l with ⟨row, chip, n, m, rn⟩
  cases chip <;> simp only [sIdx9, statesX9, newStates, sS0B, sS10B, sS10S, List.mem_append, List.mem_range,
    List.mem_cons, List.not_mem_nil]
  · exact Or.inl (stIdx_lt _)
  all_goals simp

/-- **One-hot**: the twin's state columns of a row. -/
theorem colX9_onehot (l : LX9) (fst lst : F) : ∀ j ∈ statesX9,
    colX9 H pd idOf l fst lst j = if j = sIdx9 l then 1 else 0 := by
  intro j hj
  simp only [statesX9, newStates, sS0B, sS10B, sS10S, List.mem_append, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hj
  rcases l with ⟨row, chip, n, m, rn⟩
  have hs := stIdx_lt rn.st
  simp only [nStates] at hs hj
  cases chip
  · have e1 : sIdx9 ⟨row, .old, n, m, rn⟩ = stIdx rn.st := rfl
    have e2 : colX9 H pd idOf ⟨row, .old, n, m, rn⟩ fst lst j = colX H pd rn fst lst j := rfl
    rw [e1, e2]
    rcases hj with hj | rfl | rfl | rfl
    · rw [colX_st H pd rn fst lst j hj]
      by_cases h : stIdx rn.st = j
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)]
    all_goals
      rw [ComplJ9ACompRow.colX_ge69 H pd rn fst lst _ (by norm_num), if_neg (by omega)]
  · have e2 : colX9 H pd idOf ⟨row, .s0B, n, m, rn⟩ fst lst j = colS0B H pd idOf rn n fst lst j := rfl
    have e1 : sIdx9 ⟨row, .s0B, n, m, rn⟩ = 123 := rfl
    rw [e1, e2]
    rcases hj with hj | rfl | rfl | rfl
    · rw [colS0B, if_pos hj, if_neg (by omega)]
    all_goals simp [colS0B]
  · have e2 : colX9 H pd idOf ⟨row, .s10B, n, m, rn⟩ fst lst j = colS10B H pd idOf rn n fst lst j := rfl
    have e1 : sIdx9 ⟨row, .s10B, n, m, rn⟩ = 124 := rfl
    rw [e1, e2]
    rcases hj with hj | rfl | rfl | rfl
    · rw [colS10B, if_pos hj, if_neg (by omega)]
    all_goals simp [colS10B]
  · have e2 : colX9 H pd idOf ⟨row, .s10S, n, m, rn⟩ fst lst j = colS10S H pd idOf n m rn fst lst j := rfl
    have e1 : sIdx9 ⟨row, .s10S, n, m, rn⟩ = 125 := rfl
    rw [e1, e2]
    rcases hj with hj | rfl | rfl | rfl
    · simp only [colS10S]; rw [if_pos hj, if_neg (by omega)]
    all_goals simp [colS10S]

end Cols

/-! ## 3. The three label reads at a row -/

theorem list_sum_ite {K : Type} [AddCommMonoid K] (X : ℕ → K) :
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

section Eval
variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
variable (kind : VarKind) (eK : Env K) (eF : Env F) (l : LX9) (fst lst : F)
  (hcol : ∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF = colX9 H pd idOf l fst lst i)
include hcol

theorem key_read (L : List (Option ℕ)) (hL : okKey L = true) (γ : ℕ) :
    evalMQ (rlcKeyL (F := ℚ) kind γ 0 L) eK eF =
      rlcL (eK.chal γ) 0 ((labV (colX9 H pd idOf l 0 0) L).map (algebraMap F K)) := by
  rw [HonestWalkX.evalMQ_rlcKeyL kind eK eF _ γ hcol 0 L, ← labV_fl H pd idOf l fst lst L hL]
  simp only [labV, List.map_map]
  rfl

theorem curLX9_read :
    evalMQ (curLX (F := ℚ) kind) eK eF =
      rlcL (eK.chal chalGammaW) 0 ((labV (colX9 H pd idOf l 0 0) labelColsX).map (algebraMap F K)) :=
  key_read H pd idOf kind eK eF l fst lst hcol labelColsX labelCols_ge19 chalGammaW

theorem childSumX9_read :
    evalMQ (childSumX9 (F := ℚ) kind (sIdx9 l)) eK eF =
      ∑ i ∈ Finset.range (childrenX9 (sIdx9 l)).length, eK.chal chalAlphaW ^ (i + 1) *
        rlcL (eK.chal chalGammaW) 0
          ((labV (colX9 H pd idOf l 0 0) ((childrenX9 (sIdx9 l)).getD i [])).map (algebraMap F K)) := by
  unfold childSumX9
  rw [Nock.NockVMROM.Thm54.VclL.Handle.evalMQ_sumM, List.map_map]
  simp only [Function.comp_def]
  rw [Nock.NockVMROM.Thm54.VclL.Handle.zipIdx_sum_aux [] (fun q1 q2 => evalMQ (MixedExpr.Mul (MixedExpr.Pow
    (MixedExpr.Var .challenge chalAlphaW) (q2 + 1)) (rlcKeyL kind chalGammaW 0 q1) : MixedExpr ℚ) eK eF)
    (childrenX9 (sIdx9 l)) 0]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < (childrenX9 (sIdx9 l)).length := Finset.mem_range.mp hi
  have hmem : (childrenX9 (sIdx9 l)).getD i [] ∈ childrenX9 (sIdx9 l) := by
    rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem hi'
  simp only [evalMQ, zero_add]
  rw [key_read H pd idOf kind eK eF l fst lst hcol _ (okKey_of_mem (sIdx9_mem l) hmem)]

theorem ccLX9_read :
    evalMQ (ccLX9 (F := ℚ) kind) eK eF =
      ∑ i ∈ Finset.range (childrenX9 (sIdx9 l)).length, eK.chal chalAlphaW ^ (i + 1) *
        rlcL (eK.chal chalGammaW) 0
          ((labV (colX9 H pd idOf l 0 0) ((childrenX9 (sIdx9 l)).getD i [])).map (algebraMap F K)) := by
  rw [← childSumX9_read H pd idOf kind eK eF l fst lst hcol]
  unfold ccLX9
  rw [Nock.NockVMROM.Thm54.VclL.Handle.evalMQ_sumM, List.map_map]
  have : ∀ j ∈ statesX9, ((fun g => evalMQ g eK eF) ∘ fun st =>
      (MixedExpr.Scale (kv kind st) (childSumX9 kind st) : MixedExpr ℚ)) j =
      if j = sIdx9 l then evalMQ (childSumX9 (F := ℚ) kind j) eK eF else 0 := by
    intro j hj
    have hc : evalQ (kv (F := ℚ) kind j) eF = if j = sIdx9 l then 1 else 0 := by
      simp only [kv, hcol, colX9_onehot H pd idOf l fst lst j hj]
    show algebraMap F K (evalQ (kv (F := ℚ) kind j) eF) * evalMQ (childSumX9 (F := ℚ) kind j) eK eF = _
    rw [hc]; split_ifs <;> simp
  rw [List.map_congr_left this]
  exact list_sum_ite _ _ _ statesX9_nodup (sIdx9_mem l)

theorem cmLX9_read :
    evalMQ (cmLX9 (F := ℚ) kind) eK eF = eK.chal chalAlphaW ^ (childrenX9 (sIdx9 l)).length := by
  unfold cmLX9
  rw [Nock.NockVMROM.Thm54.VclL.Handle.evalMQ_sumM, List.map_map]
  have : ∀ j ∈ statesX9, ((fun g => evalMQ g eK eF) ∘ fun st =>
      (MixedExpr.Scale (kv kind st) (.Pow (.Var .challenge chalAlphaW) (childrenX9 st).length) :
        MixedExpr ℚ)) j =
      if j = sIdx9 l then eK.chal chalAlphaW ^ (childrenX9 j).length else 0 := by
    intro j hj
    have hc : evalQ (kv (F := ℚ) kind j) eF = if j = sIdx9 l then 1 else 0 := by
      simp only [kv, hcol, colX9_onehot H pd idOf l fst lst j hj]
    show algebraMap F K (evalQ (kv (F := ℚ) kind j) eF) * eK.chal chalAlphaW ^ (childrenX9 j).length = _
    rw [hc]; split_ifs <;> simp
  rw [List.map_congr_left this]
  exact list_sum_ite (fun j => eK.chal chalAlphaW ^ (childrenX9 j).length) _ _ statesX9_nodup (sIdx9_mem l)

end Eval

/-! ## 4. `ReadsAt9` from the child link -/

section Link
variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)

/-- **`ReadsAt9` on any BFS list whose nodes all satisfy the child link**, at the node value `nodeV9`. -/
theorem readsAt9_of_link (W : List (NTree LX9)) (hW : ∀ u ∈ W, ChildLink9 (F := F) H pd idOf u) (α γ : K) :
    ReadsAt9 (F := F) H pd idOf W (nodeV9 (F := F) H pd idOf γ) α γ := by
  intro j hj1 hjh kind eK eF hα hγ hcol
  have hlt : j - 1 < W.length := by omega
  have hget : W[j - 1]? = some W[j - 1] := List.getElem?_eq_getElem hlt
  set u := W[j - 1] with hu
  have hrow : rowAt9 W j = u.label := by simp [rowAt9, hget, hu]
  rw [hrow] at hcol
  have hlink := hW u (List.getElem_mem hlt)
  unfold ChildLink9 at hlink
  have hlen : (childrenX9 (sIdx9 u.label)).length = u.children.length := by
    simpa using congrArg List.length hlink
  have hfo : Walk.foCol W j = u.children.length := by simp [Walk.foCol, hget]
  refine ⟨?_, ?_, ?_⟩
  · rw [curLX9_read H pd idOf kind eK eF _ _ _ hcol, hγ]
    simp [Walk.curCol, hget, nodeV9, nodeLab9]
  · rw [ccLX9_read H pd idOf kind eK eF _ _ _ hcol, hα, hγ, hfo, Walk.sum_Icc_one_eq_range, hlen]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < u.children.length := Finset.mem_range.mp hi
    have hi2 : i < (childrenX9 (sIdx9 u.label)).length := by omega
    have hL : labV (colX9 H pd idOf u.label 0 0) ((childrenX9 (sIdx9 u.label)).getD i []) =
        nodeLab9 (F := F) H pd idOf u.children[i] := by
      have h1 := congrArg (fun L => L[i]?) hlink
      simp only [List.getElem?_map, List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi2,
        Option.map_some, Option.some.injEq] at h1
      rw [List.getD_eq_getElem _ _ hi2]; exact h1
    rw [hL]
    simp [Walk.chldCol, hget, List.getElem?_eq_getElem hi', nodeV9]
  · rw [cmLX9_read H pd idOf kind eK eF _ _ _ hcol, hα, hfo, hlen]

end Link

/-! ## 5. The child link of the honest J-9 A tree -/

section Struct

/-- **The children of a generated `s10` row**: the two operand runs, then the edit chain. -/
theorem s10_kids {R : Nock.Jet.Registry} {v : NTree SkelX} (hv : GenNode R v) (hst : v.label.state = .s10) :
    ∃ c1 c2 c3, v.children = [c1, c2, c3] ∧ GenNode R c1 ∧ GenNode R c2 ∧ ChainNode c3 := by
  obtain ⟨m, hm⟩ := hv
  have hsem := genX_rowSem hm
  obtain ⟨a, B, D, hf⟩ : ∃ a B D, v.label.formula = .cell (.atom 10) (.cell (.cell (.atom a) B) D) := by
    simp only [RowNX.SemN, rowOfSkelX, hst] at hsem
    obtain ⟨h1, h2, h3, h4, a, h5, -⟩ := hsem
    refine ⟨a, tlN (hdN (tlN v.label.formula)), tlN (tlN v.label.formula), ?_⟩
    generalize v.label.formula = f at h1 h2 h3 h4 h5 ⊢
    rcases f with _ | ⟨f1, f2⟩
    · simp at h2
    · simp only [hdN, tlN] at h1 h3 h4 h5 ⊢
      subst h1
      rcases f2 with _ | ⟨g1, g2⟩
      · simp at h3
      · simp only [hdN, tlN] at h4 h5 ⊢
        rcases g1 with _ | ⟨k1, k2⟩
        · simp at h4
        · simp only [hdN, tlN] at h5 ⊢
          subst h5; rfl
  rw [hf] at hm
  cases m with
  | zero => simp [genComputeSkeletonX] at hm
  | succ m =>
    simp only [genComputeSkeletonX] at hm
    rcases h1 : genComputeSkeletonX R m v.label.subject B with _ | ⟨tN, new⟩ <;>
      rcases h2 : genComputeSkeletonX R m v.label.subject D with _ | ⟨tO, old⟩ <;>
      simp only [h1, h2, reduceCtorEq] at hm
    rcases h3 : Noun.edit a new old with _ | e <;> simp only [h3, reduceCtorEq, Option.some.injEq,
      Prod.mk.injEq] at hm
    obtain ⟨hv', -⟩ := hm
    rw [← hv']
    exact ⟨_, _, _, rfl, genNode_of h1, genNode_of h2, chainNode_genChain h3⟩

theorem chipOf_s0B {k : SkelX} (h : (chipOf k).1 = .s0B) : k.state = .s0 := by
  unfold chipOf at h
  cases hst : k.state <;> simp only [hst] at h <;> first | rfl | (split at h <;> simp at h) | simp at h

theorem childrenX9_old (st : StateX) : childrenX9 (stIdx st) = childrenX (stIdx st) := by cases st <;> rfl

end Struct

section Tree
variable {F : Type} [Field F]
variable (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX (hlX childNounsX ChildLinkX tripOf genX_childLink
  chain_childLink rowOfSkelX_trip)

/-- The label of a non-segment row is its `(s, f, e)` handles. -/
theorem lab_lift (l : LX9) (h : l.chip ≠ .s10S) :
    labV (colX9 H pd idOf l 0 0) labelColsX = hlX (F := F) H (l.rn.s, l.rn.f, l.rn.e) := by
  rcases l with ⟨row, chip, n, m, rn⟩
  cases chip <;> simp_all [colX9, colS0B, colS10B, labV, labelColsX, labX, xS, xF, xE, hdX, colX, hN, hlX]

theorem nodeLab_gen (c : NTree SkelX) : nodeLab9 (F := F) H pd idOf (genX9T c) = hlX H (tripOf c) := by
  rw [nodeLab9, lab_lift H pd idOf _ (by rw [genX9T_label]; exact ComplJ9AReads.chipOf_ne_s10S _), genX9T_label]
  simp only
  rw [rowOfSkelX_trip]; rfl

theorem nodeLab_lift (c : NTree SkelX) : nodeLab9 (F := F) H pd idOf (liftT c) = hlX H (tripOf c) := by
  rw [nodeLab9, lab_lift H pd idOf _ (by rw [liftT_label]; simp [liftL]), liftT_label]
  simp only [liftL]
  rw [rowOfSkelX_trip]; rfl

/-- The label of a segment node: its routed formula handle at columns 27 / 28. -/
theorem lab_seg (n m : ℕ) (s e : Noun) : nodeLab9 (F := F) H pd idOf (segT n m s e) =
    [hk H s, hv H s, (if m = top n ∧ ringChar F ≤ n then 2 else 3),
      (if m = top n ∧ ringChar F ≤ n then (idOf n : F) else ((64 * idOf n + m : ℕ) : F)), hk H e, hv H e] := by
  rw [nodeLab9, segT_label]
  simp [colX9, colS10S, labV, labelColsX, labX, xS, xF, xE, hdX, colX, hN, segRow]

/-- J-8's child reads at an old row. -/
theorem old_reads (r : RowNX)
    (hAt : r.st = .s10L → hk (F := F) H (.atom (chainAxis r.f / 2)) = 0 ∧
      hv (F := F) H (.atom (chainAxis r.f / 2)) = ((chainAxis r.f / 2 : ℕ) : F)) :
    (childrenX (stIdx r.st)).map (labV (colX H pd r 0 0)) = (childNounsX r).map (hlX (F := F) H) := by
  cases hst : r.st <;>
    simp [childrenX, childNounsX, hst, stIdx, labV, labX, labAtom, hlX,
      xS, xF, xE, xSf1, xSf2, xFh, xFt, xFth, xFtt, xFtth, xFttt, xM, hdX, colX, hN, cV, vX]
  all_goals (obtain ⟨h1, h2⟩ := hAt hst; simp [h1, h2])

/-- **The child link at a J-8 row** (old chip, J-8 children with their J-8 labels). -/
theorem link_old (u : NTree LX9) (v : NTree SkelX) (hchip : u.label.chip = .old)
    (hrn : u.label.rn = rowOfSkelX v.label)
    (hkids : u.children.map (nodeLab9 (F := F) H pd idOf) = v.children.map fun c => hlX H (tripOf c))
    (hJ : ChildLinkX v)
    (hAt : (rowOfSkelX v.label).st = .s10L →
      hk (F := F) H (.atom (chainAxis (rowOfSkelX v.label).f / 2)) = 0 ∧
      hv (F := F) H (.atom (chainAxis (rowOfSkelX v.label).f / 2)) =
        ((chainAxis (rowOfSkelX v.label).f / 2 : ℕ) : F)) :
    ChildLink9 (F := F) H pd idOf u := by
  unfold ChildLink9
  have hs : sIdx9 u.label = stIdx (rowOfSkelX v.label).st := by simp [sIdx9, hchip, hrn]
  rw [hkids, hs, childrenX9_old, ComplJ9ACompRow.colX9_old H pd idOf _ _ _ hchip, hrn,
    old_reads H pd _ hAt, ← hJ, List.map_map]
  rfl

end Tree

/-! ## 6. Every node of the honest J-9 A tree satisfies the child link -/

section Honest
variable {F : Type} [Field F]
variable (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX (hlX childNounsX ChildLinkX tripOf genX_childLink
  chain_childLink rowOfSkelX_trip)
variable {H}

theorem hk_small (hH : HdlOK (ringChar F) H) {x : ℕ} (hx : x < ringChar F) :
    hk (F := F) H (.atom x) = 0 ∧ hv (F := F) H (.atom x) = (x : F) := by
  simp [hk, hv, hH.small x hx]

/-- **Lifted J-8 chain nodes** (axis `< 2^62`): J-8's `s10L` / `s10T` child link. -/
theorem link_chain (hH : HdlOK (ringChar F) H) (hpl : 2 ^ 62 ≤ ringChar F) {v : NTree SkelX}
    (hv : ChainNode v) (hax : chainAxis v.label.formula < 2 ^ 62) :
    ChildLink9 (F := F) H pd idOf (liftT v) := by
  refine link_old H pd idOf (liftT v) v (by rw [liftT_label]; rfl) (by rw [liftT_label]; rfl) ?_
    (chain_childLink hv) ?_
  · simp only [liftT, mapNTree_children, List.map_map]
    exact List.map_congr_left fun c _ => nodeLab_lift H pd idOf c
  · intro _
    rw [ComplJ9AGen.rowOfSkelX_f]
    exact hk_small hH (by omega)

/-- The closing `s10T` node is a leaf. -/
theorem link_tNode (X Y : Noun) : ChildLink9 (F := F) H pd idOf (tNode X Y) := rfl

theorem lab_tNode (X Y : Noun) : nodeLab9 (F := F) H pd idOf (tNode X Y) = hlX H (X, .atom 1, Y) := by
  rw [nodeLab9, lab_lift H pd idOf _ (by simp [tNode])]; rfl

theorem tripOf_genChain (s e : Noun) (k : ℕ) : tripOf (genChain s e k) = (s, .atom k, e) := by
  obtain ⟨h1, h2, h3, -⟩ := genChainF_label s e k k
  simp [tripOf, genChain, h1, h2, h3]

/-- **Segment nodes**: the chain at the segment read, then the next segment's routed handle
`(3, 64·id + m − 1)` or the closing row's `(0, 1)`. -/
theorem link_seg (hH : HdlOK (ringChar F) H) (hpl : 2 ^ 62 ≤ ringChar F) (n m : ℕ) (s e : Noun)
    (hm : m ≤ top n) : ChildLink9 (F := F) H pd idOf (segT n m s e) := by
  cases m with
  | zero =>
    show (childrenX9 125).map (labV (colS10S H pd idOf n 0 (segRow n 0 s e) 0 0)) =
      [nodeLab9 H pd idOf (liftT (genChain s e (segRd n 0))),
        nodeLab9 H pd idOf (tNode (segX n 0 s) (segX n 0 e))]
    rw [nodeLab_lift, lab_tNode, tripOf_genChain]
    obtain ⟨h1, h2⟩ := hk_small (F := F) hH (x := 1) (by omega)
    simp [childrenX9, labV, labX, hlX, xS, xM, xE, xFtth, xFttt, hdX, kLabX, vLabX, colS10S, colX, hN,
      segRow, h1, h2]
  | succ m =>
    show (childrenX9 125).map (labV (colS10S H pd idOf n (m + 1) (segRow n (m + 1) s e) 0 0)) =
      [nodeLab9 H pd idOf (liftT (genChain s e (segRd n (m + 1)))),
        nodeLab9 H pd idOf (segT n m (segX n (m + 1) s) (segX n (m + 1) e))]
    rw [nodeLab_lift, lab_seg, tripOf_genChain]
    have hne : m ≠ top n := by omega
    simp [childrenX9, labV, labX, hlX, xS, xM, xE, xFtth, xFttt, hdX, kLabX, vLabX, colS10S, colX, hN,
      segRow, hne]

end Honest

section Gen
variable {F : Type} [Field F]
variable (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX (hlX childNounsX ChildLinkX tripOf genX_childLink
  chain_childLink rowOfSkelX_trip)
variable {H}

/-- **A big op-10 row (`s10B`)**: J-8's two operand children, then the segment chain root, whose routed formula
handle `(2, id)` / `(3, 64·id + top n)` is the row's `(kLab, vLab)`. -/
theorem link_s10B (hH : HdlOK (ringChar F) H) (hpu : ringChar F ≤ 2 ^ 64)
    (hid : ∀ n, ringChar F ≤ n → idOf n = (H (.atom n)).2)
    {R : Nock.Jet.Registry} {v : NTree SkelX} (hv : GenNode R v) (hB : (chipOf v.label).1 = .s10B) :
    ChildLink9 (F := F) H pd idOf (genX9T v) := by
  obtain ⟨hst, hn, hbig⟩ := chipOf_s10B hB
  obtain ⟨c1, c2, c3, hch, hg1, hg2, hc3⟩ := s10_kids hv hst
  have hJ : ChildLinkX v := by obtain ⟨m, hm⟩ := hv; exact genX_childLink hm
  have hsem := semN9_gen hv
  rw [genX9T_label] at hsem
  unfold SemN9 at hsem
  simp only [hB] at hsem
  obtain ⟨-, -, hftth, -⟩ := hsem
  have hrst : (rowOfSkelX v.label).st = .s10 := by rw [ComplJ9AGen.rowOfSkelX_st, hst]
  have hrs : (rowOfSkelX v.label).sf2 = kidE v.label 1 ∧
      (rowOfSkelX v.label).e = v.label.evaluation := by simp [rowOfSkelX, hst]
  unfold ChildLinkX at hJ
  rw [hch] at hJ
  have hcn : childNounsX (rowOfSkelX v.label) =
      [((rowOfSkelX v.label).s, (rowOfSkelX v.label).fttt, (rowOfSkelX v.label).sf1),
       ((rowOfSkelX v.label).s, (rowOfSkelX v.label).ftt, (rowOfSkelX v.label).sf2),
       ((rowOfSkelX v.label).sf2, (rowOfSkelX v.label).ftth, (rowOfSkelX v.label).e)] := by
    unfold childNounsX; rw [hrst]
  rw [hcn] at hJ
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hJ
  obtain ⟨t1, t2, -, -⟩ := hJ
  have k1 : kid9 v.label c1 (genX9T c1) = genX9T c1 := by simp [kid9, genNode_not_chain hg1]
  have k2 : kid9 v.label c2 (genX9T c2) = genX9T c2 := by simp [kid9, genNode_not_chain hg2]
  have k3 : kid9 v.label c3 (genX9T c3) =
      segT (chipOf v.label).2 (top (chipOf v.label).2) (kidE v.label 1) v.label.evaluation := by
    simp [kid9, hB, chainNode_isChain hc3]
  unfold ChildLink9
  rw [genX9T_children, hch]
  simp only [List.map_cons, List.map_nil, k1, k2, k3]
  rw [nodeLab_gen, nodeLab_gen, lab_seg, t1, t2, ← hrs.1, ← hrs.2, genX9T_label]
  have h62 : 2 ^ 62 ≤ (chipOf v.label).2 := hn ▸ hbig
  generalize (chipOf v.label).2 = n at hftth h62 ⊢
  generalize rowOfSkelX v.label = r at hftth ⊢
  have hs : sIdx9 ⟨rowX9 v.label, (chipOf v.label).1, n, 0, r⟩ = 124 := by simp [sIdx9, hB]
  have hc : colX9 (F := F) H pd idOf ⟨rowX9 v.label, (chipOf v.label).1, n, 0, r⟩ 0 0 =
      colS10B (F := F) H pd idOf r n 0 0 := by
    simp [colX9, hB]
  rw [hs, hc]
  by_cases hp : ringChar F ≤ n
  · simp [childrenX9, labV, labX, hlX, xS, xFttt, xFtt, xSf1, xSf2, xE, hdX, kLabX, vLabX, colS10B, colX, hN,
      hp, hftth, hid n hp, HonestCompX.hv]
  · have htop : top n = 1 := ComplJ9AReads.top_field h62 (by omega)
    simp [childrenX9, labV, labX, hlX, xS, xFttt, xFtt, xSf1, xSf2, xE, hdX, kLabX, vLabX, colS10B, colX, hN,
      hp, htop]

/-- **A reclassified generated row** (`old`, `s0B`, `s10B`). -/
theorem link_gen (hH : HdlOK (ringChar F) H) (hpu : ringChar F ≤ 2 ^ 64)
    (hid : ∀ n, ringChar F ≤ n → idOf n = (H (.atom n)).2)
    {R : Nock.Jet.Registry} {v : NTree SkelX} (hv : GenNode R v) :
    ChildLink9 (F := F) H pd idOf (genX9T v) := by
  have hJ : ChildLinkX v := by obtain ⟨m, hm⟩ := hv; exact genX_childLink hm
  rcases hc : (chipOf v.label).1 with _ | _ | _ | _
  · refine link_old H pd idOf _ v (by rw [genX9T_label]; exact hc) (by rw [genX9T_label]) ?_ hJ ?_
    · rw [genX9T_children, List.map_map]
      refine List.map_congr_left fun c _ => ?_
      have : kid9 v.label c (genX9T c) = genX9T c := by simp [kid9, hc]
      simp only [Function.comp_apply, this, nodeLab_gen]
    · intro h
      exfalso
      have := genNode_not_chain hv
      rw [ComplJ9AGen.rowOfSkelX_st] at h
      rw [h] at this
      simp [StateX.isChain] at this
  · have hst := chipOf_s0B hc
    have hnil : v.children = [] := by
      have h0 : childNounsX (rowOfSkelX v.label) = [] := by
        unfold childNounsX; rw [ComplJ9AGen.rowOfSkelX_st, hst]
      have := hJ
      unfold ChildLinkX at this
      rw [h0] at this
      simpa using this
    unfold ChildLink9
    rw [genX9T_children, hnil, genX9T_label]
    simp [sIdx9, hc, childrenX9]
  · exact link_s10B pd idOf hH hpu hid hv hc
  · exact absurd hc (ComplJ9AReads.chipOf_ne_s10S _)

/-- **Every node of the J-9 A tree of a generated run satisfies the child link.** -/
theorem link_all (hH : HdlOK (ringChar F) H) (hpl : 2 ^ 62 ≤ ringChar F) (hpu : ringChar F ≤ 2 ^ 64)
    (hid : ∀ n, ringChar F ≤ n → idOf n = (H (.atom n)).2)
    {R : Nock.Jet.Registry} {fuel : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R fuel s f = some (t, r)) {u : NTree LX9} (hu : InTree (genX9T t) u) :
    ChildLink9 (F := F) H pd idOf u := by
  rcases genX9T_inTree h hu with ⟨v, -, hv, rfl⟩ | ⟨v, hv, hax, rfl⟩ |
      ⟨n, m, s', e, new, hn, hm, he, rfl⟩ | ⟨X, Y, rfl⟩
  · exact link_gen pd idOf hH hpu hid hv
  · exact link_chain pd idOf hH hpl hv hax
  · exact link_seg pd idOf hH hpl n m s' e hm
  · exact link_tNode pd idOf X Y

end Gen

/-! ## 7. `hrd` of `computeChipVCLHX9_honest_sat` at the honest tree -/

section Main
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **The walk label reads of the honest J-9 A tree** (generic field form): at every BFS row of
`genX9T t`, the three reads of the twin walk gate are the tree's walk values at `nodeV9`. -/
theorem readsAt9_honest (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (hH : HdlOK (ringChar F) H) (hpl : 2 ^ 62 ≤ ringChar F) (hpu : ringChar F ≤ 2 ^ 64)
    (hid : ∀ n, ringChar F ≤ n → idOf n = (H (.atom n)).2)
    {R : Nock.Jet.Registry} {fuel : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R fuel s f = some (t, r)) (α γ : K) :
    ReadsAt9 (F := F) H pd idOf (bfsForest [genX9T t]) (nodeV9 (F := F) H pd idOf γ) α γ :=
  readsAt9_of_link H pd idOf _ (fun u hu => link_all pd idOf hH hpl hpu hid h
    (Nock.NockVMROM.Thm54.TraceGen.inTree_of_mem_bfsForest_singleton hu)) α γ

end Main

section ZMod
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]

/-- **`hrd` at `F = ZMod p`, `idOf = idOf9 p nA H (fieldAx9 p (rowsOfT9 t))`** (the exact `idOf` of the honest
data), for `2^62 ≤ p ≤ 2^64` (Goldilocks). -/
theorem readsAt9_honest_zmod (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (nA : ℕ)
    (hH : HdlOK p H) (hpl : 2 ^ 62 ≤ p) (hpu : p ≤ 2 ^ 64)
    {R : Nock.Jet.Registry} {fuel : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R fuel s f = some (t, r)) (α γ : K) :
    ReadsAt9 (F := ZMod p) H pd
      (ComplJ9AChains.idOf9 p nA H (ComplJ9AData.fieldAx9 p (rowsOfT9 t))) (bfsForest [genX9T t])
      (nodeV9 (F := ZMod p) H pd (ComplJ9AChains.idOf9 p nA H (ComplJ9AData.fieldAx9 p (rowsOfT9 t))) γ) α γ := by
  have hc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  refine readsAt9_honest H pd _ (by rw [hc]; exact hH) (by rw [hc]; exact hpl) (by rw [hc]; exact hpu)
    (fun n hn => ComplJ9AChains.idOf9_big (by rw [hc] at hn; exact hn)) h α γ

end ZMod




end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReadsAt

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReadsAt
#print axioms readsAt9_of_link
#print axioms s10_kids
#print axioms link_old
#print axioms link_chain
#print axioms link_seg
#print axioms link_s10B
#print axioms link_gen
#print axioms link_all
#print axioms readsAt9_honest
#print axioms readsAt9_honest_zmod
end Axioms
