/-
 Nock/Edit/GenXDet.lean

 **Determinism of the execution tree on the fragment `{0, 7, 10, autocons}`.**

 A genuine ℕ-level execution tree `T` (`GenuineNX R T`) whose root has subject `s` and formula
 `f`, where `f` lies in the fragment `P1Frag` (opcodes 0, 7, 10 and autocons only, checked
 syntactically all the way down), is exactly the tree that the generator `genX` builds for
 `(s, f)`, relabelled to `RowX`:

 * `genuineNX_chain_eq` — the edit chain is fixed top-down: a genuine chain subtree with subject
 `old`, atom formula `a` and evaluation `e` is `genChainF old e k a` for any depth fuel
 `k ≥ a`.
 * **`genuineNX_eq_genX`** — under `R.Faithful`, `genX R n s f = some (t, r)` and a genuine `T`
 rooted at `(s, f)` give `T = relabelT SkelX.row t` and `skelOfT T = t` (the `SkelX` lift of
 `T`, whose `kids` field is its children's labels, is the generated tree itself).
 * `genuineNX_bfs_eq_genX` — the BFS label lists agree.

 `R.Faithful` is used only to identify the `s10` row's evaluation with the generated edit
 result (through `genuineNX_holdsN`, `genX_sound` and `evalN_deterministic`); every other node
 is fixed by its kid inputs and its row output. The fragment hypothesis excludes op 11, where
 a genuine tree may choose `s11d` while the generator chose `s11j` (or the converse), and
 keeps every formula syntactic (no op 2 / op 9 runtime formulas).
-/
import Nock.Edit.GenX
import Nock.Edit.GenuineNX
import Nock.NockVMROM.Thm54.ExactTraversal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.Edit.GenX

open Nock Nock.Walk Nock.ComputeTable Nock.Jet Nock.Edit
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputedWindow

/-! ## §1 The fragment and the tree maps -/

/-- **The fragment `{0, 7, 10, autocons}`**, syntactically at every subformula. -/
inductive P1Frag : Noun → Prop
  | op0 (ax : ℕ) : P1Frag (.cell (.atom 0) (.atom ax))
  | op7 {b c : Noun} : P1Frag b → P1Frag c → P1Frag (.cell (.atom 7) (.cell b c))
  | op10 {ax : ℕ} {c d : Noun} :
      P1Frag c → P1Frag d → P1Frag (.cell (.atom 10) (.cell (.cell (.atom ax) c) d))
  | cons {b c d : Noun} : P1Frag (.cell b c) → P1Frag d → P1Frag (.cell (.cell b c) d)

/-- Relabel a tree. -/
def relabelT {α β : Type} (g : α → β) : NTree α → NTree β
  | .node l cs => .node (g l) (cs.map (relabelT g))

@[simp] theorem relabelT_node {α β : Type} (g : α → β) (l : α) (cs : List (NTree α)) :
    relabelT g (.node l cs) = .node (g l) (cs.map (relabelT g)) := by
  simp [relabelT]

@[simp] theorem relabelT_label {α β : Type} (g : α → β) (t : NTree α) :
    (relabelT g t).label = g t.label := by
  cases t; simp [relabelT, NTree.label]

/-- `relabelT` is `mapNTree`. -/
theorem relabelT_eq_mapNTree {α β : Type} (g : α → β) :
    ∀ t : NTree α, relabelT g t = mapNTree g t
  | .node l cs => by
    simp only [relabelT_node, mapNTree, NTree.node.injEq, true_and]
    exact List.map_congr_left (fun u _ => relabelT_eq_mapNTree g u)

/-- **The `SkelX` lift of a `RowX` tree**: every node's `kids` field is its children's labels. -/
def skelOfT : NTree RowX → NTree SkelX
  | .node r cs =>
    .node ⟨r.state, r.subject, r.formula, r.evaluation, cs.map NTree.label⟩ (cs.map skelOfT)

@[simp] theorem skelOfT_node (r : RowX) (cs : List (NTree RowX)) :
    skelOfT (.node r cs) =
      .node ⟨r.state, r.subject, r.formula, r.evaluation, cs.map NTree.label⟩ (cs.map skelOfT) := by
  simp [skelOfT]

/-! ## §2 Shapes -/

theorem state_op0 {st : StateX} {ax : ℕ} (h : FormulaShapeX st (.cell (.atom 0) (.atom ax))) :
    st = .s0 := by
  cases st <;> simp [FormulaShapeX, FormulaShape] at h ⊢

theorem state_op7 {st : StateX} {b c : Noun} (h : FormulaShapeX st (.cell (.atom 7) (.cell b c))) :
    st = .s7 := by
  cases st <;> simp [FormulaShapeX, FormulaShape] at h ⊢

theorem state_op10 {st : StateX} {ax : ℕ} {c d : Noun}
    (h : FormulaShapeX st (.cell (.atom 10) (.cell (.cell (.atom ax) c) d))) : st = .s10 := by
  cases st <;> simp [FormulaShapeX, FormulaShape] at h ⊢

theorem state_cons {st : StateX} {b c d : Noun} (h : FormulaShapeX st (.cell (.cell b c) d)) :
    st = .cons := by
  cases st <;> simp [FormulaShapeX, FormulaShape] at h ⊢

/-- A genuine node with a cell formula is a real (non-chain) node. -/
theorem isChain_false_of_cell {R : Registry} {T : NTree RowX} (hT : GenuineNX R T) {x y : Noun}
    (hf : T.label.formula = .cell x y) : T.label.state.isChain = false := by
  cases hT with
  | @node lbl kids shape _ _ _ _ =>
    simp only [NTree.label_node] at hf ⊢
    rw [hf] at shape
    cases hst : lbl.state <;> rw [hst] at shape <;> simp [FormulaShapeX, StateX.isChain] at shape ⊢

/-- The evaluation of a genuine real node equals the generated result. -/
theorem eval_eq_of_genX {R : Registry} (hR : R.Faithful) {n : ℕ} {s f r : Noun} {t : NTree SkelX}
    (h : genX R n s f = some (t, r)) {T : NTree RowX} (hT : GenuineNX R T)
    (hs : T.label.subject = s) (hf : T.label.formula = f)
    (hreal : T.label.state.isChain = false) : T.label.evaluation = r := by
  obtain ⟨m1, h1⟩ := genuineNX_holdsN hR hT hreal
  obtain ⟨m2, h2⟩ := genX_sound hR h
  simp only at h1 h2
  rw [hs, hf] at h1
  exact evalN_deterministic h1 h2

/-! ## §3 The edit chain -/

/-- **The chain is fixed top-down by its root**: a genuine chain subtree with subject `old`, atom
formula `a` and evaluation `e` is the generated chain at any depth fuel `k ≥ a`. -/
theorem genuineNX_chain_eq {R : Registry} {old e : Noun} :
    ∀ (k a : ℕ) {T : NTree RowX}, GenuineNX R T → T.label.state.isChain = true →
      T.label.subject = old → T.label.formula = .atom a → T.label.evaluation = e → a ≤ k →
      T = relabelT SkelX.row (genChainF old e k a) ∧ skelOfT T = genChainF old e k a := by
  intro k
  induction k with
  | zero =>
    intro a T hT hch hs hf he hk
    have ha : a = 0 := by omega
    subst ha
    cases hT with
    | @node lbl kids shape _ _ _ _ =>
      simp only [NTree.label_node] at hch hf
      rw [hf] at shape
      cases hst : lbl.state <;> rw [hst] at shape hch <;>
        simp [FormulaShapeX, StateX.isChain] at shape hch
  | succ k ih =>
    intro a T hT hch hs hf he hk
    cases hT with
    | @node lbl kids shape inputs output roles children =>
      obtain ⟨st, s', f', e'⟩ := lbl
      simp only [NTree.label_node] at hch hs hf he
      subst hs hf he
      cases st <;> simp only [StateX.isChain, reduceCtorEq] at hch
      · -- s10L
        obtain ⟨ax, hax, h2⟩ := shape
        simp only [Noun.atom.injEq] at hax
        subst hax
        rcases kids with _ | ⟨k0, _ | ⟨k1, rest⟩⟩ <;>
          simp only [List.map, KidInputsNX, KidInputsX] at inputs
        obtain ⟨hs0, hf0⟩ := inputs
        simp only [RowOutputNX, List.map_cons, List.map_nil] at output
        obtain ⟨he0, -⟩ := output
        simp only [chainAxis] at hf0
        have hc0 : k0.label.state.isChain = true := roles 0 (by simp)
        obtain ⟨rfl, hk0⟩ := ih (a / 2) (children k0 (by simp)) hc0 hs0 hf0 he0 (by omega)
        simp only [genChainF, h2, ↓reduceIte, mkX, relabelT_node, List.map, skelOfT_node,
          relabelT_label, SkelX.row, hk0, true_and]
      · -- s10T
        simp only [FormulaShapeX, Noun.atom.injEq] at shape
        subst shape
        rcases kids with _ | ⟨k0, rest⟩ <;>
          simp only [List.map, KidInputsNX, KidInputsX, reduceCtorEq] at inputs
        simp [genChainF, mkX, SkelX.row]

/-! ## §4 The tree -/

/-- **Determinism on the fragment.** A genuine tree rooted at `(s, f)` with `f ∈ P1Frag` is the
generated tree of `(s, f)` (relabelled), and its `SkelX` lift is the generated tree itself. -/
theorem genuineNX_eq_genX {R : Registry} (hR : R.Faithful) {f : Noun} (hfrag : P1Frag f) :
    ∀ {n : ℕ} {s r : Noun} {t : NTree SkelX} {T : NTree RowX},
      genX R n s f = some (t, r) → GenuineNX R T →
      T.label.subject = s → T.label.formula = f →
      T = relabelT SkelX.row t ∧ skelOfT T = t := by
  induction hfrag with
  | op0 ax =>
    intro n s r t T h hT hs hf
    rcases n with _ | n
    · simp [genComputeSkeletonX] at h
    cases hsl : Noun.slot ax s with
    | none => simp [genComputeSkeletonX, hsl] at h
    | some v =>
      simp only [genComputeSkeletonX, hsl, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases hT with
      | @node lbl kids shape inputs output roles children =>
        obtain ⟨st, s', f', e'⟩ := lbl
        simp only [NTree.label_node] at hs hf
        subst hs hf
        obtain rfl := state_op0 shape
        simp only [KidInputsNX, KidInputsX, List.map_eq_nil_iff] at inputs
        subst inputs
        simp only [RowOutputNX, op0Axis, hsl, Option.some.injEq] at output
        subst output
        simp [mkX, SkelX.row]
  | @op7 b c _ _ ihb ihc =>
    intro n s r t T h hT hs hf
    rcases n with _ | n
    · simp [genComputeSkeletonX] at h
    cases hb : genX R n s b with
    | none => simp [genComputeSkeletonX, hb] at h
    | some p =>
      obtain ⟨tH, sb⟩ := p
      cases hc : genX R n sb c with
      | none => simp [genComputeSkeletonX, hb, hc] at h
      | some q =>
        obtain ⟨tM, r'⟩ := q
        have h0 := h
        simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases hT with
        | @node lbl kids shape inputs output roles children =>
          obtain ⟨st, s', f', e'⟩ := lbl
          simp only [NTree.label_node] at hs hf
          subst hs hf
          obtain rfl := state_op7 shape
          rcases kids with _ | ⟨kM, _ | ⟨kH, _ | ⟨k2, rest⟩⟩⟩ <;>
            simp only [List.map, KidInputsNX, KidInputsX] at inputs
          obtain ⟨hsH, hfH, hsM, hfM⟩ := inputs
          simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at hfH hfM
          simp only [RowOutputNX, List.map_cons, List.map_nil] at output
          obtain ⟨rfl, hH⟩ := ihb hb (children kH (by simp)) hsH hfH
          rw [relabelT_label, SkelX.row, (genX_label hb).2.2.1] at hsM
          obtain ⟨rfl, hM⟩ := ihc hc (children kM (by simp)) hsM hfM
          rw [relabelT_label] at output
          simp only [SkelX.row, (genX_label hc).2.2.1] at output
          subst output
          simp [mkX, SkelX.row, hH, hM]
  | @op10 ax c d _ _ ihc ihd =>
    intro n s r t T h hT hs hf
    rcases n with _ | n
    · simp [genComputeSkeletonX] at h
    cases hc : genX R n s c with
    | none => simp [genComputeSkeletonX, hc] at h
    | some p =>
      obtain ⟨tN, new⟩ := p
      cases hd : genX R n s d with
      | none => simp [genComputeSkeletonX, hc, hd] at h
      | some q =>
        obtain ⟨tO, old⟩ := q
        cases hed : Noun.edit ax new old with
        | none => simp [genComputeSkeletonX, hc, hd, hed] at h
        | some e =>
          have h0 := h
          simp only [genComputeSkeletonX, hc, hd, hed, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hreal := isChain_false_of_cell hT hf
          have hev := eval_eq_of_genX hR h0 hT hs hf hreal
          cases hT with
          | @node lbl kids shape inputs output roles children =>
            obtain ⟨st, s', f', e'⟩ := lbl
            simp only [NTree.label_node] at hs hf hev
            subst hs hf hev
            obtain rfl := state_op10 shape
            rcases kids with _ | ⟨kN, _ | ⟨kO, _ | ⟨kE, _ | ⟨k3, rest⟩⟩⟩⟩ <;>
              simp only [List.map, KidInputsNX, KidInputsX] at inputs
            obtain ⟨hsN, hfN, hsO, hfO, hsE, hfE⟩ := inputs
            simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail,
              op10Axis] at hfN hfO hfE
            simp only [RowOutputNX, List.map_cons, List.map_nil] at output
            obtain ⟨-, hE⟩ := output
            obtain ⟨rfl, hN⟩ := ihc hc (children kN (by simp)) hsN hfN
            obtain ⟨rfl, hO⟩ := ihd hd (children kO (by simp)) hsO hfO
            rw [relabelT_label, SkelX.row, (genX_label hd).2.2.1] at hsE
            have hcE : kE.label.state.isChain = true := roles 2 (by simp)
            obtain ⟨rfl, hEk⟩ := genuineNX_chain_eq ax ax (children kE (by simp)) hcE hsE hfE hE le_rfl
            simp [mkX, SkelX.row, genChain, hN, hO, hEk]
  | @cons b c d _ _ ihbc ihd =>
    intro n s r t T h hT hs hf
    rcases n with _ | n
    · simp [genComputeSkeletonX] at h
    cases hbc : genX R n s (.cell b c) with
    | none => simp [genComputeSkeletonX, hbc] at h
    | some p =>
      obtain ⟨tl0, l⟩ := p
      cases hd : genX R n s d with
      | none => simp [genComputeSkeletonX, hbc, hd] at h
      | some q =>
        obtain ⟨tr0, r'⟩ := q
        simp only [genComputeSkeletonX, hbc, hd, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases hT with
        | @node lbl kids shape inputs output roles children =>
          obtain ⟨st, s', f', e'⟩ := lbl
          simp only [NTree.label_node] at hs hf
          subst hs hf
          obtain rfl := state_cons shape
          rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, rest⟩⟩⟩ <;>
            simp only [List.map, KidInputsNX, KidInputsX] at inputs
          obtain ⟨hs0, hf0, hs1, hf1⟩ := inputs
          simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at hf0 hf1
          simp only [RowOutputNX, List.map_cons, List.map_nil] at output
          obtain ⟨rfl, h0⟩ := ihbc hbc (children k0 (by simp)) hs0 hf0
          obtain ⟨rfl, h1⟩ := ihd hd (children k1 (by simp)) hs1 hf1
          simp only [relabelT_label, SkelX.row, (genX_label hbc).2.2.1,
            (genX_label hd).2.2.1] at output
          subst output
          simp [mkX, SkelX.row, h0, h1]

/-- **The BFS label lists agree** (the label-level form of `genuineNX_eq_genX`). -/
theorem genuineNX_bfs_eq_genX {R : Registry} (hR : R.Faithful) {f : Noun} (hfrag : P1Frag f)
    {n : ℕ} {s r : Noun} {t : NTree SkelX} {T : NTree RowX} (h : genX R n s f = some (t, r))
    (hT : GenuineNX R T) (hs : T.label.subject = s) (hf : T.label.formula = f) :
    (bfsForest [T]).map NTree.label = (bfsForest [t]).map (fun u => u.label.row) := by
  obtain ⟨rfl, -⟩ := genuineNX_eq_genX hR hfrag h hT hs hf
  have := bfsForest_mapNTree SkelX.row [t]
  rw [relabelT_eq_mapNTree]
  simp only [List.map_cons, List.map_nil] at this
  rw [this, List.map_map]
  congr 1
  funext u
  simp [mapNTree_label]

end Nock.Edit.GenX

#print axioms Nock.Edit.GenX.genuineNX_chain_eq
#print axioms Nock.Edit.GenX.genuineNX_eq_genX
#print axioms Nock.Edit.GenX.genuineNX_bfs_eq_genX
