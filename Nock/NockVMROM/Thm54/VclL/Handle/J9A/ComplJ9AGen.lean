/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AGen.lean

The J-9 A generator is a RELABELLING of J-8's `genX` tree (`Gen.lean` / `GenX.lean` untouched):
  * an op-0 row whose axis atom is `≥ 2^62` (field or big) is chip state `s0B`;
  * an op-10 row whose axis atom `n` is `≥ 2^62` is chip state `s10B`, and its edit chain (child 2, J-8's
    `genChain old e n`) is REPLACED by the segment chain `segT n (top n) old e`: per segment `m` (top down) one
    `s10S` pseudo-row (formula the atom `segAx n m`), whose first child is J-8's `s10L` chain at the segment read
    `segRd n m < 2^33` (verbatim `genChain`), and whose second child is the next segment, ending at an `s10T` row
    at the atom `1`;
  * every other row is J-8's (chip state `old`).

  The label `LX9` carries the semantic row (`RowX9`), the chip state and, on `s0B` / `s10B` / `s10S` rows, the axis
  atom `n` and the segment index `m` (the ids are assigned at the data level, not here).

  * `chain_genuine`: J-8's chain is field-genuine at the J-9 A ISA (`GenuineSkelFX9`).
  * **`segT_genuine`**: the segment chain of a successful edit at a nonzero axis is field-genuine at the J-9 A ISA
    (every `s10S` row obeys `KidInputsX9` / `RowOutputFX9` with `m' = 32·m`, `r = n mod 2^(32 m)`); so by
    `genuineFX9_sem` its root satisfies `ChainOK n old e`.
  * `genX9T_label`, `segT_label`: the root rows.
  * **`genX9T_inTree`**: every node of the J-9 A tree of a generated run is a reclassified generated node, a lifted
    J-8 chain node, or a segment node (`Node9`; closed under children, `node9_children`).
  * `LX9.rn`: the honest noun row (`rowOfSkelX` on lifted rows, `segRow` on `s10S`, `tRow` on a segment end);
    **`SemN9`** (what the J-9 A gates need of a row: J-8's `SemN` with the axis `< 2^62` on old `s0` / `s10` rows,
    J-8's `SemN` with the axis `≥ 2^62` on `s0B` / `s10B`, the segment split on `s10S`); **`rowsOfT9_semN9`**:
    every row of `rowsOfT9 t` (BFS) satisfies it.
-/
import Nock.Edit.SemanticsX9
import Nock.Edit.GenX
import Nock.Edit.GenXRows
import Nock.NockVMROM.Thm54.ExactTraversal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 (mapNTree mapNTree_label mapNTree_children)
open Nock.NockVMROM.Thm54.ComputedWindow (op0Axis)
open Nock.J9A.NounAx (top segAx segRd nxtAx segAx_decomp segAx_next nxtAx_zero segRd_pos segAx_top)

/-! ## 1. Labels -/

/-- The chip state of a J-9 A row beyond its semantic state: J-8's, or one of the three new selectors. -/
inductive ChipSt9
  | old | s0B | s10B | s10S
deriving DecidableEq, Repr

/-- **A J-9 A tree label**: the semantic row, the chip state, the axis atom and the segment index. -/
structure LX9 where
  row : RowX9
  chip : ChipSt9
  n : ℕ
  m : ℕ
  /-- the honest noun row (J-8's `rowOfSkelX` on lifted rows; `segRow` on `s10S`, `tRow` on a segment end) -/
  rn : RowNX
deriving DecidableEq, Repr

/-- J-8's semantic row at the J-9 A ISA. -/
def rowX9 (k : SkelX) : RowX9 := ⟨StateX9.ofX k.state, k.subject, k.formula, k.evaluation⟩

/-- A J-8 label, chip state `old`. -/
def liftL (k : SkelX) : LX9 := ⟨rowX9 k, .old, 0, 0, rowOfSkelX k⟩

/-- A J-8 subtree at the J-9 A labels. -/
def liftT : NTree SkelX → NTree LX9 := mapNTree liftL

/-- The semantic view. -/
def semT : NTree LX9 → NTree RowX9 := mapNTree LX9.row

/-! ## 2. The segment chain -/

/-- The segment-`m` subnoun of `s` (`atom 0` if undefined). -/
def segX (n m : ℕ) (s : Noun) : Noun := (Noun.slot (segRd n m) s).getD (.atom 0)

/-- The honest noun row of an `s10S` pseudo-row (state slot `s10L`: the chip state is `ChipSt9.s10S`): the
pair `sf1 = s`, `sf2 = e`, the segment slots `ftth = /[seg] s`, `fttt = /[seg] e`, and `m` the segment read. -/
def segRow (n m : ℕ) (s e : Noun) : RowNX :=
  { st := .s10L, s, f := .atom (segAx n m), e, ftth := segX n m s, fttt := segX n m e, sf1 := s, sf2 := e,
    m := .atom (segRd n m) }

/-- The honest noun row of a segment chain's closing `s10T` row. -/
def tRow (X Y : Noun) : RowNX := { st := .s10T, s := X, f := .atom 1, e := Y }

/-- The closing `s10T` node. -/
def tNode (X Y : Noun) : NTree LX9 := .node ⟨⟨.s10T, X, .atom 1, Y⟩, .old, 0, 0, tRow X Y⟩ []

/-- One `s10S` pseudo-row: J-8's chain at the segment read, then `next`. -/
def segNode (n m : ℕ) (s e : Noun) (next : NTree LX9) : NTree LX9 :=
  .node ⟨⟨.s10S, s, .atom (segAx n m), e⟩, .s10S, n, m, segRow n m s e⟩ [liftT (genChain s e (segRd n m)), next]

/-- **The segment chain** of an edit at axis `n` from segment `m` down, on `old ⇝ e`. -/
def segT (n : ℕ) : ℕ → Noun → Noun → NTree LX9
  | 0, s, e => segNode n 0 s e (tNode (segX n 0 s) (segX n 0 e))
  | m + 1, s, e => segNode n (m + 1) s e (segT n m (segX n (m + 1) s) (segX n (m + 1) e))

theorem segT_label (n m : ℕ) (s e : Noun) :
    (segT n m s e).label = ⟨⟨.s10S, s, .atom (segAx n m), e⟩, .s10S, n, m, segRow n m s e⟩ := by
  cases m <;> rfl

/-! ## 3. The generator -/

/-- `2^62 ≤ a`: the axis is served by the axis chip (field `[2^62, p)` or big `≥ p`). -/
def big62 (a : ℕ) : Bool := decide (2 ^ 62 ≤ a)

/-- The chip state and axis atom of a J-8 row. -/
def chipOf (k : SkelX) : ChipSt9 × ℕ :=
  match k.state with
  | .s0 => if big62 (op0Axis k.formula) then (.s0B, op0Axis k.formula) else (.old, 0)
  | .s10 => if big62 (op10Axis k.formula) then (.s10B, op10Axis k.formula) else (.old, 0)
  | _ => (.old, 0)

/-- The J-9 A image of child `c` of a J-8 row `k`: on an `s10B` row the edit chain (the one chain child) becomes
the segment chain. -/
def kid9 (k : SkelX) (c : NTree SkelX) (g : NTree LX9) : NTree LX9 :=
  if (chipOf k).1 = .s10B ∧ c.label.state.isChain = true then
    segT (chipOf k).2 (top (chipOf k).2) (kidE k 1) k.evaluation
  else g

/-- **The J-9 A generator** (tree level): J-8's tree, reclassified, with every big op-10 chain replaced by its
segment chain. -/
def genX9T : NTree SkelX → NTree LX9
  | .node k ks =>
    .node ⟨rowX9 k, (chipOf k).1, (chipOf k).2, 0, rowOfSkelX k⟩ (ks.map fun c => kid9 k c (genX9T c))

theorem genX9T_label (t : NTree SkelX) :
    (genX9T t).label = ⟨rowX9 t.label, (chipOf t.label).1, (chipOf t.label).2, 0, rowOfSkelX t.label⟩ := by
  cases t; rw [genX9T]; rfl

theorem genX9T_row (t : NTree SkelX) : (genX9T t).label.row = rowX9 t.label := by
  rw [genX9T_label]

/-! ## 4. Field genuineness of the chains -/

section Genuine
variable (q : ℕ)

@[simp] theorem semT_node (l : LX9) (ks : List (NTree LX9)) :
    semT (.node l ks) = .node l.row (ks.map semT) := by
  simp only [semT, mapNTree]

@[simp] theorem liftT_node (k : SkelX) (ks : List (NTree SkelX)) :
    liftT (.node k ks) = .node (liftL k) (ks.map liftT) := by
  simp only [liftT, mapNTree]

@[simp] theorem semT_label (x : NTree LX9) : (semT x).label = x.label.row := mapNTree_label _ _

@[simp] theorem liftT_label (x : NTree SkelX) : (liftT x).label = liftL x.label := mapNTree_label _ _

/-- **J-8's chain is field-genuine at the J-9 A ISA.** -/
theorem chain_genuine : ∀ (k a : ℕ) {old e : Noun}, ChainOK a old e → 1 ≤ a → a ≤ k + 1 →
    GenuineSkelFX9 q (semT (liftT (genChainF old e k a)))
  | 0, a, old, e, hc, h1, h2 => by
    have ha : a = 1 := by omega
    subst ha
    simp only [genChainF, mkX, liftT_node, semT_node, List.map_nil]
    exact .node rfl rfl trivial (fun i h => absurd h (by simp)) (fun k hk => absurd hk (by simp))
  | k + 1, a, old, e, hc, h1, h2 => by
    by_cases h2a : 2 ≤ a
    · have ih := chain_genuine k (a / 2) (chainOK_half hc) (by omega) (by omega)
      have hsib := hc 0 (by simpa using h2a)
      simp only [pow_zero, Nat.div_one] at hsib
      obtain ⟨hs, he, hf, hch⟩ := genChainF_label old e k (a / 2)
      simp only [genChainF, h2a, ite_true, mkX, liftT_node, semT_node, List.map_cons, List.map_nil]
      refine .node ?_ ?_ ?_ ?_ ?_
      · exact ⟨a, rfl, h2a⟩
      · simp only [liftL, rowX9, StateX9.ofX, KidInputsX9, List.map_cons, List.map_nil, semT_label,
          liftT_label]
        exact ⟨hs, by rw [hf]; rfl⟩
      · simp only [liftL, rowX9, StateX9.ofX, RowOutputFX9, List.map_cons, List.map_nil, semT_label,
          liftT_label]
        exact ⟨he, hsib⟩
      · intro i hi
        simp only [List.length_cons, List.length_nil] at hi
        have : i = 0 := by omega
        subst this
        simp only [List.getElem_cons_zero, semT_label, liftT_label, liftL, rowX9, StateX9.isChain_ofX, hch]
        rfl
      · intro x hx
        simp only [List.mem_singleton] at hx
        subst hx
        exact ih
    · have ha : a = 1 := by omega
      subst ha
      simp only [genChainF, mkX, liftT_node, semT_node, List.map_nil, show ¬ (2 ≤ 1) by omega, ite_false]
      exact .node rfl rfl trivial (fun i h => absurd h (by simp)) (fun k hk => absurd hk (by simp))

theorem chainAxis_atom (a : ℕ) : chainAxis (.atom a) = a := rfl

/-- The end of a segment chain: an `s10T` row. -/
theorem tNode_genuine (X Y : Noun) :
    GenuineSkelFX9 q (semT (tNode X Y)) := by
  simp only [tNode, semT_node, List.map_nil]
  exact .node rfl rfl trivial (fun i h => absurd h (by simp)) (fun k hk => absurd hk (by simp))

/-- **One `s10S` row is genuine** given the edit decomposition at its segment: `s ⇝ e` is an edit at the segment
read `a = segRd n m` whose slots are `X`, `Y`, and `next` is a genuine chain node `X ⇝ Y` at axis `2^m' + r`. -/
theorem segNode_genuine (n m : ℕ) {s e X Y : Noun} {m' r : ℕ} (next : NTree LX9) (hr : r < 2 ^ m')
    (hpos : 1 ≤ segRd n m) (hd : segAx n m = segRd n m * 2 ^ m' + r)
    (hc : ChainOK (segRd n m) s e) (hX : Noun.slot (segRd n m) s = some X)
    (hY : Noun.slot (segRd n m) e = some Y)
    (hns : next.label.row.subject = X) (hne : next.label.row.evaluation = Y)
    (hnf : next.label.row.formula = .atom (2 ^ m' + r)) (hnc : next.label.row.state.isChain = true)
    (hng : GenuineSkelFX9 q (semT next)) :
    GenuineSkelFX9 q (semT (segNode n m s e next)) := by
  have hcg := chain_genuine q (segRd n m) (segRd n m) hc hpos (by omega)
  obtain ⟨hs0, he0, hf0, hch0⟩ := genChainF_label s e (segRd n m) (segRd n m)
  simp only [segNode, genChain, semT_node, List.map_cons, List.map_nil]
  refine .node ⟨_, rfl⟩ ?_ ?_ ?_ ?_
  · simp only [KidInputsX9, List.map_cons, List.map_nil, semT_label, liftT_label, liftL, rowX9]
    refine ⟨hs0, m', r, hr, ?_, ?_, ?_⟩
    · rw [hf0]; exact hpos
    · rw [hf0, hd]; rfl
    · rw [hnf]; rfl
  · simp only [RowOutputFX9, List.map_cons, List.map_nil, semT_label, liftT_label, liftL, rowX9, hf0,
      chainAxis_atom]
    exact ⟨he0, X, Y, hX, hY, hns, hne⟩
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · simp only [List.getElem_cons_zero, semT_label, liftT_label, liftL, rowX9, StateX9.isChain_ofX, hch0,
        chainPosX9]
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero, semT_label, hnc, chainPosX9]
  · intro x hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hcg
    · exact hng

/-- The edit at a segment axis splits at the segment read. -/
theorem seg_split {n m : ℕ} (hn : n ≠ 0) (hm : m ≤ top n) {new s e : Noun}
    (he : Noun.edit (segAx n m) new s = some e) :
    ∃ X Y, Noun.slot (segRd n m) s = some X ∧ Noun.slot (segRd n m) e = some Y ∧
      ChainOK (segRd n m) s e ∧ Noun.edit (nxtAx n m) new X = some Y := by
  have hd := segAx_decomp n m hm
  have hpos := segRd_pos hn m hm
  have hr := Nock.J9A.NounAx.nxtAx_lt_pow n m
  rw [hd, Nock.J9A.NounComp.edit_comp _ _ _ _ _ hpos hr] at he
  rcases hX : Noun.slot (segRd n m) s with _ | X
  · rw [hX] at he; cases he
  rw [hX] at he
  simp only [Option.bind_some] at he
  rcases hY' : Noun.edit (2 ^ (32 * m) + n % 2 ^ (32 * m)) new X with _ | Y
  · rw [hY'] at he; cases he
  rw [hY'] at he
  simp only [Option.bind_some] at he
  obtain ⟨hc, hsl⟩ := chainOK_of_edit _ he
  exact ⟨X, Y, rfl, hsl, hc, hY'⟩

/-- **The segment chain of a successful edit is field-genuine at the J-9 A ISA.** -/
theorem segT_genuine (n : ℕ) (hn : n ≠ 0) : ∀ (m : ℕ) {new s e : Noun}, m ≤ top n →
    Noun.edit (segAx n m) new s = some e → GenuineSkelFX9 q (semT (segT n m s e)) := by
  intro m
  induction m with
  | zero =>
    intro new s e hm he
    obtain ⟨X, Y, hX, hY, hc, -⟩ := seg_split hn hm he
    have hsX : segX n 0 s = X := by simp [segX, hX]
    have heY : segX n 0 e = Y := by simp [segX, hY]
    simp only [segT]
    rw [hsX, heY]
    refine segNode_genuine q n 0 _ (m' := 0) (r := 0) (by norm_num) (segRd_pos hn 0 hm) ?_ hc hX hY rfl rfl
      rfl rfl (tNode_genuine q X Y)
    rw [segAx_decomp n 0 hm]; simp [Nat.mod_one]
  | succ m ih =>
    intro new s e hm he
    obtain ⟨X, Y, hX, hY, hc, hnx⟩ := seg_split hn hm he
    have hnext : Noun.edit (segAx n m) new X = some Y := by
      have := segAx_next n (m + 1) hm (by omega)
      simp only [Nat.add_sub_cancel] at this
      rw [this]; exact hnx
    have hsX : segX n (m + 1) s = X := by simp [segX, hX]
    have heY : segX n (m + 1) e = Y := by simp [segX, hY]
    simp only [segT]
    rw [hsX, heY]
    refine segNode_genuine q n (m + 1) _ (Nock.J9A.NounAx.nxtAx_lt_pow n (m + 1)) (segRd_pos hn _ hm)
      (segAx_decomp n (m + 1) hm) hc hX hY ?_ ?_ ?_ ?_ (ih (by omega) hnext)
    · rw [segT_label]
    · rw [segT_label]
    · rw [segT_label]
      have := segAx_next n (m + 1) hm (by omega)
      simp only [Nat.add_sub_cancel] at this
      simp only [this, nxtAx]
    · rw [segT_label]; rfl

/-- **The segment chain at the top segment carries the edit's chain**: `ChainOK n old e` at its root
(`genuineFX9_sem`), i.e. the segments compose to the big axis. -/
theorem segT_top_genuine {n : ℕ} (hn : n ≠ 0) {new old e : Noun} (he : Noun.edit n new old = some e) :
    GenuineSkelFX9 q (semT (segT n (top n) old e)) := by
  apply segT_genuine q n hn (top n) le_rfl
  rw [segAx_top]; exact he

end Genuine

/-! ## 5. Every node of the J-9 A tree -/

theorem genX9T_node (k : SkelX) (ks : List (NTree SkelX)) :
    genX9T (.node k ks) = .node ⟨rowX9 k, (chipOf k).1, (chipOf k).2, 0, rowOfSkelX k⟩
      (ks.map fun c => kid9 k c (genX9T c)) := by
  rw [genX9T]

theorem genX9T_children (t : NTree SkelX) :
    (genX9T t).children = t.children.map fun c => kid9 t.label c (genX9T c) := by
  cases t; rw [genX9T_node]; rfl

/-- On a chain row the generator is the plain lift. -/
theorem genX9T_genChainF (old e : Noun) : ∀ k a, genX9T (genChainF old e k a) = liftT (genChainF old e k a)
  | 0, a => by
    simp only [genChainF, mkX, genX9T_node, liftT_node, List.map_nil, chipOf, liftL]
  | k + 1, a => by
    by_cases h : 2 ≤ a
    · simp only [genChainF, h, ite_true, mkX, genX9T_node, liftT_node, List.map_cons, List.map_nil, chipOf,
        liftL, kid9, genX9T_genChainF old e k (a / 2), reduceCtorEq, false_and, ite_false]
    · simp only [genChainF, h, ite_false, mkX, genX9T_node, liftT_node, List.map_nil, chipOf, liftL]

theorem genX9T_chain {v : NTree SkelX} (hv : ChainNode v) : genX9T v = liftT v := by
  obtain ⟨old, e, k, a, rfl, -⟩ := hv
  exact genX9T_genChainF old e k a

/-- `GenX.genX_children` with the chain child's axis: it is the row's op-10 axis. -/
theorem genX_children9 {R : Nock.Jet.Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) : ∀ k ∈ t.children, GenNode R k ∨
      (ChainNode k ∧ k.label.formula = .atom (op10Axis t.label.formula) ∧ t.label.state = .s10) := by
  induction n, s, f using genComputeSkeletonX.induct R generalizing t r
  all_goals first | (simp_all [genComputeSkeletonX]; done) | skip
  case case3 n s b c d tl l tr r' hd hbc ih1 ih2 =>
    simp only [genComputeSkeletonX, hd, hbc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case5 n s ax r' hs =>
    simp only [genComputeSkeletonX, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case7 n s u =>
    simp only [genComputeSkeletonX, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp
  case case8 n s b c tl l tr r1 hc hb t2 r2 hm ih1 ih2 ih3 =>
    simp only [genComputeSkeletonX, hb, hc, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case11 n s u t2 v hx ih =>
    simp only [genComputeSkeletonX, hx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case13 n s u t0 v hx ih =>
    simp only [genComputeSkeletonX, hx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case15 n s b c tl l tr r1 hc hb ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case17 n s b c d tC hb t2 r1 hc ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case19 n s b c d tC hb t2 r1 hc ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case22 n s b c t1 r1 hb t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case25 n s b c t1 r1 hb t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hb, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case28 n s ax c t1 core hc arm harm t2 r2 hm ih1 ih2 =>
    simp only [genComputeSkeletonX, hc, harm, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case32 n s ax c d tl new tr old hd hc e he ih1 ih2 =>
    simp only [genComputeSkeletonX, hc, hd, he, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false]
    rintro k (rfl | rfl | rfl)
    · exact Or.inl (genNode_of hc)
    · exact Or.inl (genNode_of hd)
    · refine Or.inr ⟨chainNode_genChain he, ?_, rfl⟩
      rw [genChain, (genChainF_label _ _ _ _).2.2.1]; rfl
  case case35 n s b clue body t1 v hcl r1 hj ih1 =>
    simp only [genComputeSkeletonX, hcl, hj, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case36 n s b clue body t1 v hcl hj t2 r1 hB ih1 ih2 =>
    simp only [genComputeSkeletonX, hcl, hj, hB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))
  case case39 n s b body t2 r1 hB ih1 =>
    simp only [genComputeSkeletonX, hB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false, false_imp_iff, imp_true_iff]
    try (rintro k (rfl | rfl | rfl) <;> exact Or.inl (genNode_of (by assumption)))


/-- A segment-chain node: an `s10S` row of a successful edit, or the closing `s10T` row. -/
def SegNode9 (u : NTree LX9) : Prop :=
  (∃ n m s e new, n ≠ 0 ∧ m ≤ top n ∧ Noun.edit (segAx n m) new s = some e ∧ u = segT n m s e) ∨
  (∃ X Y, u = tNode X Y)

/-- **The node classes of the J-9 A tree of `t`**: a reclassified generated node of `t`, a lifted J-8 chain node
at an axis `< 2^62`, or a segment node. -/
def Node9 (R : Nock.Jet.Registry) (t : NTree SkelX) (u : NTree LX9) : Prop :=
  (∃ v, InTree t v ∧ GenNode R v ∧ u = genX9T v) ∨
  (∃ v, ChainNode v ∧ chainAxis v.label.formula < 2 ^ 62 ∧ u = liftT v) ∨ SegNode9 u

/-- A generated `s10` row edits at its axis atom. -/
theorem genNode_s10_edit {R : Nock.Jet.Registry} {v : NTree SkelX} (hv : GenNode R v)
    (hst : v.label.state = .s10) :
    Noun.edit (op10Axis v.label.formula) (kidE v.label 0) (kidE v.label 1) = some v.label.evaluation := by
  obtain ⟨m, hm⟩ := hv
  have h := genX_rowSem hm
  simp only [RowNX.SemN, rowOfSkelX, hst] at h
  obtain ⟨-, hf, hft, hfth, a, ha, he⟩ := h
  rw [hf, hft, hfth, ha]
  exact he

theorem big62_iff (a : ℕ) : big62 a = true ↔ 2 ^ 62 ≤ a := by simp [big62]

theorem chipOf_s10B {k : SkelX} (h : (chipOf k).1 = .s10B) :
    k.state = .s10 ∧ (chipOf k).2 = op10Axis k.formula ∧ 2 ^ 62 ≤ op10Axis k.formula := by
  unfold chipOf at h ⊢
  cases hst : k.state <;> simp only [hst] at h ⊢ <;> try (simp at h; done)
  · by_cases hb : big62 (op0Axis k.formula) = true <;> simp only [hb, ite_true, ite_false, reduceCtorEq] at h
  · by_cases hb : big62 (op10Axis k.formula) = true
    · simp only [hb, ite_true]
      exact ⟨trivial, trivial, (big62_iff _).1 hb⟩
    · simp only [hb, ite_false, reduceCtorEq] at h

theorem small_of_not_s10B {k : SkelX} (hst : k.state = .s10) (h : (chipOf k).1 ≠ .s10B) :
    op10Axis k.formula < 2 ^ 62 := by
  by_contra hc
  apply h
  have hb : big62 (op10Axis k.formula) = true := (big62_iff _).2 (by omega)
  unfold chipOf
  rw [hst]
  simp only [hb, ite_true]

theorem inTree_child {t v c : NTree SkelX} (hv : InTree t v) (hc : c ∈ v.children) : InTree t c :=
  InTree_trans hv (.sub hc (.here c))

theorem chainNode_child_axis {v w : NTree SkelX} (hv : ChainNode v) (hw : w ∈ v.children) :
    chainAxis w.label.formula ≤ chainAxis v.label.formula := by
  obtain ⟨old, e, k, a, rfl, -⟩ := hv
  cases k with
  | zero => simp [genChainF] at hw
  | succ k =>
    by_cases h2 : 2 ≤ a
    · simp only [genChainF, h2, ite_true, mkX_children, List.mem_singleton] at hw
      subst hw
      rw [(genChainF_label _ _ _ _).2.2.1, (genChainF_label _ _ _ _).2.2.1]
      exact Nat.div_le_self _ _
    · simp [genChainF, h2] at hw

theorem genNode_not_chain {R : Nock.Jet.Registry} {c : NTree SkelX} (hc : GenNode R c) :
    c.label.state.isChain = false := by
  obtain ⟨m, hm⟩ := hc
  exact (genX_label hm).2.2.2

/-- **The node classes are closed under children.** -/
theorem node9_children {R : Nock.Jet.Registry} {t : NTree SkelX} {u : NTree LX9} (hu : Node9 R t u) :
    ∀ c ∈ u.children, Node9 R t c := by
  rcases hu with ⟨v, hvt, hv, rfl⟩ | ⟨v, hv, hax, rfl⟩ | hseg
  · obtain ⟨m, hm⟩ := hv
    have hkids := genX_children9 hm
    intro c' hc'
    rw [genX9T_children] at hc'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
    rcases hkids c hc with hg | ⟨hch, hfc, hst⟩
    · have hnc := genNode_not_chain hg
      have : kid9 v.label c (genX9T c) = genX9T c := by simp [kid9, hnc]
      rw [this]
      exact Or.inl ⟨c, inTree_child hvt hc, hg, rfl⟩
    · have hic := chainNode_isChain hch
      by_cases hB : (chipOf v.label).1 = .s10B
      · have : kid9 v.label c (genX9T c) =
            segT (chipOf v.label).2 (top (chipOf v.label).2) (kidE v.label 1) v.label.evaluation := by
          simp [kid9, hB, hic]
        rw [this]
        obtain ⟨-, hn, hbig⟩ := chipOf_s10B hB
        refine Or.inr (Or.inr (Or.inl ⟨_, _, _, _, kidE v.label 0, ?_, le_rfl, ?_, rfl⟩))
        · rw [hn]; omega
        · rw [segAx_top, hn]; exact genNode_s10_edit ⟨m, hm⟩ hst
      · have : kid9 v.label c (genX9T c) = genX9T c := by simp [kid9, hB]
        rw [this, genX9T_chain hch]
        refine Or.inr (Or.inl ⟨c, hch, ?_, rfl⟩)
        rw [hfc]
        exact small_of_not_s10B hst hB
  · intro c hc
    simp only [liftT, mapNTree_children] at hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
    exact Or.inr (Or.inl ⟨w, chainNode_children hv w hw,
      lt_of_le_of_lt (chainNode_child_axis hv hw) hax, rfl⟩)
  · rcases hseg with ⟨n, m, s, e, new, hn, hm, he, rfl⟩ | ⟨X, Y, rfl⟩
    · obtain ⟨X, Y, hX, hY, hc, hnx⟩ := seg_split hn hm he
      have hch : ChainNode (genChain s e (segRd n m)) :=
        ⟨s, e, segRd n m, segRd n m, rfl, hc, segRd_pos hn m hm, by omega⟩
      have hax : chainAxis (genChain s e (segRd n m)).label.formula < 2 ^ 62 := by
        rw [genChain, (genChainF_label _ _ _ _).2.2.1, chainAxis_atom]
        have := Nock.J9A.NounAx.segRd_lt n m
        omega
      cases m with
      | zero =>
        intro c hc'
        simp only [segT, segNode, NTree.children, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hc'
        rcases hc' with rfl | rfl
        · exact Or.inr (Or.inl ⟨_, hch, hax, rfl⟩)
        · exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩))
      | succ m =>
        intro c hc'
        simp only [segT, segNode, NTree.children, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hc'
        rcases hc' with rfl | rfl
        · exact Or.inr (Or.inl ⟨_, hch, hax, rfl⟩)
        · have hnext : Noun.edit (segAx n m) new X = some Y := by
            have := segAx_next n (m + 1) hm (by omega)
            simp only [Nat.add_sub_cancel] at this
            rw [this]; exact hnx
          refine Or.inr (Or.inr (Or.inl ⟨n, m, _, _, new, hn, by omega, ?_, rfl⟩))
          simpa [segX, hX, hY] using hnext
    · intro c hc'
      simp [tNode, NTree.children] at hc'

/-- **Every node of the J-9 A tree of a generated run is in a node class.** -/
theorem genX9T_inTree {R : Nock.Jet.Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) {u : NTree LX9} (hu : InTree (genX9T t) u) : Node9 R t u := by
  have key : ∀ {c u : NTree LX9}, InTree c u → Node9 R t c → Node9 R t u := by
    intro c u hcu
    induction hcu with
    | here => exact id
    | sub hs _ ih => exact fun hc => ih (node9_children hc _ hs)
  exact key hu (Or.inl ⟨t, .here t, genNode_of h, rfl⟩)

/-! ## 6. What the J-9 A gates need of a row (noun level) -/

/-- **`SemN9`**: J-8's `SemN` on old rows (with the op-0 / op-10 axis below `2^62`: those stay on the J-9 B
path), J-8's `SemN` plus the big axis on `s0B` / `s10B`, and the segment facts on `s10S` (an edit at the segment
axis whose read splits at `segRd`). -/
def SemN9 (R : Nock.Jet.Registry) (l : LX9) : Prop :=
  match l.chip with
  | .old => l.rn.SemN R ∧ (l.rn.st = .s0 → ∀ ax, l.rn.ft = .atom ax → ax < 2 ^ 62) ∧
      (l.rn.st = .s10 → ∀ a, l.rn.ftth = .atom a → a < 2 ^ 62)
  | .s0B => l.rn.SemN R ∧ l.rn.st = .s0 ∧ l.rn.ft = .atom l.n ∧ 2 ^ 62 ≤ l.n
  | .s10B => l.rn.SemN R ∧ l.rn.st = .s10 ∧ l.rn.ftth = .atom l.n ∧ 2 ^ 62 ≤ l.n
  | .s10S => l.n ≠ 0 ∧ l.m ≤ top l.n ∧ l.rn = segRow l.n l.m l.rn.s l.rn.e ∧
      (∃ new, Noun.edit (segAx l.n l.m) new l.rn.s = some l.rn.e) ∧ ChainOK (segRd l.n l.m) l.rn.s l.rn.e ∧
      Noun.slot (segRd l.n l.m) l.rn.s = some l.rn.ftth ∧ Noun.slot (segRd l.n l.m) l.rn.e = some l.rn.fttt

theorem op0Axis_of_semN {R : Nock.Jet.Registry} {r : RowNX} (hst : r.st = .s0) (h : r.SemN R) {ax : ℕ}
    (hft : r.ft = .atom ax) : op0Axis r.f = ax := by
  simp only [RowNX.SemN, hst] at h
  obtain ⟨-, hf, -⟩ := h
  rw [hf, hft]; rfl

theorem op10Axis_of_semN {R : Nock.Jet.Registry} {r : RowNX} (hst : r.st = .s10) (h : r.SemN R) {a : ℕ}
    (hftth : r.ftth = .atom a) : op10Axis r.f = a := by
  simp only [RowNX.SemN, hst] at h
  obtain ⟨-, hf, hft, hfth, -⟩ := h
  rw [hf, hft, hfth, hftth]; rfl

theorem rowOfSkelX_st (k : SkelX) : (rowOfSkelX k).st = k.state := by
  unfold rowOfSkelX; cases k.state <;> rfl

theorem rowOfSkelX_f (k : SkelX) : (rowOfSkelX k).f = k.formula := by
  unfold rowOfSkelX; cases k.state <;> rfl

/-- `SemN9` at a reclassified generated node. -/
theorem semN9_gen {R : Nock.Jet.Registry} {v : NTree SkelX} (hv : GenNode R v) :
    SemN9 R (genX9T v).label := by
  obtain ⟨m, hm⟩ := hv
  have h := genX_rowSem hm
  rw [genX9T_label]
  have hst := rowOfSkelX_st v.label
  have hf := rowOfSkelX_f v.label
  unfold SemN9
  simp only
  unfold chipOf
  cases hs : v.label.state
  case s0 =>
    have hst0 : (rowOfSkelX v.label).st = .s0 := by rw [hst, hs]
    by_cases hb : big62 (op0Axis v.label.formula) = true
    · simp only [hb, ite_true]
      have h' := h
      simp only [RowNX.SemN, hst0] at h'
      obtain ⟨-, -, ax, hax, -⟩ := h'
      have hax' := op0Axis_of_semN hst0 h hax
      rw [hf] at hax'
      refine ⟨h, hst0, by rw [hax, hax'], ?_⟩
      exact (big62_iff _).1 hb
    · simp only [hb, ite_false]
      refine ⟨h, ?_, ?_⟩
      swap
      · intro h10; rw [hst0] at h10; cases h10
      intro _ ax hax
      have hax' := op0Axis_of_semN hst0 h hax
      rw [hf] at hax'
      rw [← hax']
      by_contra hc
      exact hb ((big62_iff _).2 (by omega))
  case s10 =>
    have hst0 : (rowOfSkelX v.label).st = .s10 := by rw [hst, hs]
    by_cases hb : big62 (op10Axis v.label.formula) = true
    · simp only [hb, ite_true]
      have h' := h
      simp only [RowNX.SemN, hst0] at h'
      obtain ⟨-, -, -, -, a, ha, -⟩ := h'
      have ha' := op10Axis_of_semN hst0 h ha
      rw [hf] at ha'
      refine ⟨h, hst0, by rw [ha, ha'], ?_⟩
      exact (big62_iff _).1 hb
    · simp only [hb, ite_false]
      refine ⟨h, ?_, ?_⟩
      · intro h0; rw [hst0] at h0; cases h0
      intro _ a ha
      have ha' := op10Axis_of_semN hst0 h ha
      rw [hf] at ha'
      rw [← ha']
      by_contra hc
      exact hb ((big62_iff _).2 (by omega))
  all_goals
    refine ⟨h, ?_, ?_⟩ <;> intro h0 <;> rw [hst, hs] at h0 <;> cases h0

/-- **Every node of the J-9 A tree of a generated run satisfies `SemN9`.** -/
theorem semN9_of_node9 {R : Nock.Jet.Registry} {t : NTree SkelX} {u : NTree LX9} (hu : Node9 R t u) :
    SemN9 R u.label := by
  rcases hu with ⟨v, -, hv, rfl⟩ | ⟨v, hv, -, rfl⟩ | ⟨n, m, s, e, new, hn, hm, he, rfl⟩ | ⟨X, Y, rfl⟩
  · exact semN9_gen hv
  · have hc := chainNode_isChain hv
    have hsem := chainNode_rowSem R hv
    rw [liftT_label]
    have hst := rowOfSkelX_st v.label
    refine ⟨hsem, fun h0 => ?_, fun h0 => ?_⟩ <;> (simp only [liftL] at h0; rw [hst] at h0; rw [h0] at hc; cases hc)
  · obtain ⟨X, Y, hX, hY, hc, -⟩ := seg_split hn hm he
    rw [segT_label]
    refine ⟨hn, hm, rfl, ⟨new, he⟩, hc, ?_, ?_⟩
    · simp [segRow, segX, hX]
    · simp [segRow, segX, hY]
  · exact ⟨by simp [tNode, tRow, RowNX.SemN], fun h0 => by simp [tNode, tRow] at h0,
      fun h0 => by simp [tNode, tRow] at h0⟩

/-- **The J-9 A honest rows** (BFS order of the J-9 A tree). -/
def rowsOfT9 (t : NTree SkelX) : Array LX9 := ((bfsForest [genX9T t]).map fun u => u.label).toArray

/-- **Every J-9 A honest row satisfies `SemN9`.** -/
theorem rowsOfT9_semN9 {R : Nock.Jet.Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) : ∀ l ∈ (rowsOfT9 t).toList, SemN9 R l := by
  intro l hl
  simp only [rowsOfT9, List.toList_toArray, List.mem_map] at hl
  obtain ⟨u, hu, rfl⟩ := hl
  obtain ⟨c, hc, hcu⟩ := (mem_bfsForest _ _).1 hu
  simp only [List.mem_singleton] at hc
  subst hc
  exact semN9_of_node9 (genX9T_inTree h hcu)

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen
#print axioms chain_genuine
#print axioms segT_genuine
#print axioms segT_top_genuine
#print axioms genX9T_label
#print axioms node9_children
#print axioms genX9T_inTree
#print axioms semN9_of_node9
#print axioms rowsOfT9_semN9
end Axioms
