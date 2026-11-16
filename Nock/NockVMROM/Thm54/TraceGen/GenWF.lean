/-
  Nock/NockVMROM/Thm54/TraceGen/GenWF.lean

  Generator-side `ComputeTable.WF` on rendered BFS rows.

  `size8` / `size11` are encoding: every rendered fingerprint that the inverse
  gates inspect is `encC z n`, whose size coordinate is `z^leaves`.  Vacuous off `.s8` / `.cons`.

  `rlc5` is coin-genericity on `(a,b,c)`, the same species as
  `ioPoleHitGood` / `ioGammaGood` / `ioLogDerivGood`.
  Stated of challenge Inputs `⟨α, z, a, b, c⟩` against the rendered `Pub` — `Vcomp`
  does not read the RLC coins; the renderer bakes zeros into the row Inputs.

  This module does not edit `Gen.lean`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenSound
import Nock.NockVMROM.Thm54.TraceGen.Checker
import Nock.NockVMROM.Thm54.TraceGen.CubicField97
import Nock.NockVMROM.Thm54.FiniteFieldIOSoundness
import Nock.TableWFBounds
import Nock.NockVMROM.Thm54.RecordCarrier
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonFanout

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open ComputeTable
open TableWFBounds
open Nock.NockVMROM.Thm54.TraceGen.Checker

variable {K : Type} [Field K]

set_option linter.unusedSectionVars false

/-! ## Challenge Inputs vs rendered row Inputs -/

/-- Verifier-sampled compute coins.  Distinct from the renderer's baked
    `⟨α, z, 0, 0, 0⟩` (`renderOp*Row`).  `WF.rlc5` reads these; `Vcomp` does not. -/
def challengeInputs (z α a b c : K) : Inputs K := ⟨α, z, a, b, c⟩

/-- Overwrite the baked RLC coins on a rendered compute row.  `Vcomp` is
    invariant in `(a,b,c)`; `ComputeRowsAccepted` matches `cfg` Inputs. -/
def setRowCoins (a b c : K) (row : State × DTcomp K) : State × DTcomp K :=
  (row.1, ⟨row.2.1.α, row.2.1.z, a, b, c⟩, row.2.2)

@[simp] theorem setRowCoins_state (a b c : K) (row : State × DTcomp K) :
    (setRowCoins a b c row).1 = row.1 := rfl

@[simp] theorem setRowCoins_α (a b c : K) (row : State × DTcomp K) :
    (setRowCoins a b c row).2.1.α = row.2.1.α := rfl

@[simp] theorem setRowCoins_z (a b c : K) (row : State × DTcomp K) :
    (setRowCoins a b c row).2.1.z = row.2.1.z := rfl

@[simp] theorem setRowCoins_pub (a b c : K) (row : State × DTcomp K) :
    (setRowCoins a b c row).2.2 = row.2.2 := rfl

theorem Vcomp_of_same_az {inp inp' : Inputs K} {pub : Pub K} {dec : Dec K}
    (hα : inp.α = inp'.α) (hz : inp.z = inp'.z)
    (h : Vcomp inp pub dec) : Vcomp inp' pub dec := by
  obtain ⟨hf, hmr, hsv, hmem, hev⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [hz.symm] using hf
  · simpa [hα.symm] using hmr
  · unfold SVhead at hsv ⊢
    split_ifs at hsv ⊢
    · exact hsv
    · simpa [hz] using hsv
  · unfold memBlk at hmem ⊢
    cases hst : pub.state <;> simp [hst, hα, hz] at hmem ⊢ <;> exact hmem
  · unfold evalV at hev ⊢
    cases hst : pub.state <;> simp [hst, hz] at hev ⊢ <;> exact hev

theorem Vcomp_setRowCoins (a b c : K) (row : State × DTcomp K) :
    Vcomp (setRowCoins a b c row).2.1 (setRowCoins a b c row).2.2.1
      (setRowCoins a b c row).2.2.2 ↔
    Vcomp row.2.1 row.2.2.1 row.2.2.2 := by
  constructor
  · intro h
    exact Vcomp_of_same_az (inp := (setRowCoins a b c row).2.1) (inp' := row.2.1)
      rfl rfl h
  · intro h
    exact Vcomp_of_same_az (inp := row.2.1) (inp' := (setRowCoins a b c row).2.1)
      rfl rfl h

theorem bindComputeRow_setRowCoins (z a b c : K)
    {s : ComputeRowSkeleton} {row : State × DTcomp K}
    (h : BindComputeRow z s row) :
    BindComputeRow z s (setRowCoins a b c row) := by
  simpa [setRowCoins, BindComputeRow] using h

theorem computeTimestampSpecializesAt_setRowCoins (α a b c : K)
    {stamp : ComputeTimestampRow} {row : State × DTcomp K}
    (h : ComputeTimestampSpecializesAt α stamp row) :
    ComputeTimestampSpecializesAt α stamp (setRowCoins a b c row) := by
  simpa [setRowCoins, ComputeTimestampSpecializesAt] using h

theorem renderNode_pub_state (z α : K) (g : GenComputeRow K) :
    (renderNode z α g).row.2.2.1.state = g.skel.state := by
  unfold renderNode
  cases g.skel.state <;> rfl

/-- `renderNode` writes the **absolute** line-number origin `α^lnPrevExponent` into every rendered
    row.

    The RAP-faithful `ComputeTimestampSpecializesAt` deliberately does not pin `ln_prev` -- paper
    `V_comp` does not pin the first row's `ln_prev` either -- so consumers that genuinely need the
    origin (the semantic request bridge) take it as a separate hypothesis and discharge it here. -/
theorem renderNode_ln_prev (z α : K) (g : GenComputeRow K) :
    (renderNode z α g).row.2.2.1.ln_prev = α ^ g.stamp.lnPrevExponent := by
  unfold renderNode
  cases g.skel.state <;>
    simp [renderOp0Row, renderOp1Row, renderOp2Row, renderOp3Row, renderOp4Row,
      renderOp5Row, renderOp6Row, renderOp7Row, renderOp8Row, renderOp9Row,
      renderConsRow]

/-! ## Encoding sizes (`size8` / `size11`) -/

/-- OP_8 inverse-gate sizes are `z`-powers of live NPR encodings. -/
theorem renderOp8Row_sizes (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) (hz : z ≠ 0) :
    (renderOp8Row z α stamp skel).2.2.1.sf2_e.size ≠ 0 ∧
      (renderOp8Row z α stamp skel).2.2.1.s.size ≠ 0 := by
  constructor
  · change (encC z (P8Census.skeletonSubformula skel 1 .result)).size ≠ 0
    simp only [encC]
    exact pow_ne_zero _ hz
  · change (encC z skel.subject).size ≠ 0
    simp only [encC]
    exact pow_ne_zero _ hz

/-- Cons inverse-gate sizes are `z`-powers of the two evaluation children. -/
theorem renderConsRow_sizes (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) (hz : z ≠ 0) :
    (renderConsRow z α stamp skel).2.2.1.sf1_e.size ≠ 0 ∧
      (renderConsRow z α stamp skel).2.2.1.sf2_e.size ≠ 0 := by
  constructor
  · change (encC z (formulaHead skel.evaluation)).size ≠ 0
    simp only [encC]
    exact pow_ne_zero _ hz
  · change (encC z (formulaTail skel.evaluation)).size ≠ 0
    simp only [encC]
    exact pow_ne_zero _ hz

theorem renderOp8Row_size8 (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) (hz : z ≠ 0) :
    (renderOp8Row z α stamp skel).2.2.1.state = State.s8 →
      (renderOp8Row z α stamp skel).2.2.1.sf2_e.size ≠ 0 ∧
        (renderOp8Row z α stamp skel).2.2.1.s.size ≠ 0 :=
  fun _ => renderOp8Row_sizes z α stamp skel hz

theorem renderConsRow_size11 (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton) (hz : z ≠ 0) :
    (renderConsRow z α stamp skel).2.2.1.state = State.cons →
      (renderConsRow z α stamp skel).2.2.1.sf1_e.size ≠ 0 ∧
        (renderConsRow z α stamp skel).2.2.1.sf2_e.size ≠ 0 :=
  fun _ => renderConsRow_sizes z α stamp skel hz

/-! ## Per-node `WF` -/

/-- Rendered node satisfies `WF` at challenge coins `(a,b,c)`.  `size8`/`size11`
    from encoding; `rlc5` from the coin-genericity hypothesis. -/
theorem renderNode_WF (z α a b c : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (h5 : rlc5Holds a b c (renderNode z α g).row.2.2.1) :
    WF (challengeInputs z α a b c) (renderNode z α g).row.2.2.1 where
  rlc5 := (rlc5Holds_iff_wf (challengeInputs z α a b c)
    (renderNode z α g).row.2.2.1).mp h5
  size8 := by
    intro hst
    have hstate : g.skel.state = State.s8 :=
      (renderNode_pub_state z α g).symm.trans hst
    rw [renderNode_op8_row z α g hstate]
    exact renderOp8Row_sizes z α g.stamp g.skel hz
  size11 := by
    intro hst
    have hstate : g.skel.state = State.cons :=
      (renderNode_pub_state z α g).symm.trans hst
    rw [renderNode_cons_row z α g hstate]
    exact renderConsRow_sizes z α g.stamp g.skel hz

/-- Off `.s5`, `rlc5` is vacuous (`needsRlc5` is false). -/
theorem rlc5Holds_of_ne_s5 (a b c : K) (pub : Pub K)
    (h : pub.state ≠ State.s5) : rlc5Holds a b c pub := by
  intro hn
  exact (h hn.1).elim

theorem renderNode_rlc5Holds_of_ne_s5 (z α a b c : K) (g : GenComputeRow K)
    (h : g.skel.state ≠ State.s5) :
    rlc5Holds a b c (renderNode z α g).row.2.2.1 :=
  rlc5Holds_of_ne_s5 a b c _ (by simpa [renderNode_pub_state] using h)

/-- Off `.s5`, `WF` is encoding-only: `z ≠ 0`. -/
theorem renderNode_WF_of_ne_s5 (z α a b c : K) (g : GenComputeRow K)
    (hz : z ≠ 0) (h : g.skel.state ≠ State.s5) :
    WF (challengeInputs z α a b c) (renderNode z α g).row.2.2.1 :=
  renderNode_WF z α a b c g hz (renderNode_rlc5Holds_of_ne_s5 z α a b c g h)

/-! ## Tree-wide `NTree.All` `WF` -/

/-- Every rendered node of `u` satisfies `WF` once every rendered pub satisfies
    `rlc5Holds`.  Shape is `Checker.NTree.All`. -/
theorem renderRows_All_WF (z α a b c : K) (u : Walk.NTree (GenComputeRow K))
    (hz : z ≠ 0)
    (h5 : NTree.All (fun g => rlc5Holds a b c (renderNode z α g).row.2.2.1) u) :
    NTree.All (fun g => WF (challengeInputs z α a b c) g.row.2.2.1)
      (renderRows z α u) := by
  let P := fun t : Walk.NTree (GenComputeRow K) =>
    NTree.All (fun g => rlc5Holds a b c (renderNode z α g).row.2.2.1) t →
      NTree.All (fun g => WF (challengeInputs z α a b c) g.row.2.2.1)
        (renderRows z α t)
  have hP : P u := by
    apply Walk.NTree.rec (motive_1 := P)
      (motive_2 := fun ts => ∀ c ∈ ts, P c)
    · intro g ch ih hAll
      unfold NTree.All at hAll ⊢
      unfold renderRows
      refine ⟨renderNode_WF z α a b c g hz hAll.1, ?_⟩
      intro s hs
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
      exact ih c hc (hAll.2 c hc)
    · intro c hc; simp at hc
    · intro head tail ihHead ihTail c hc
      rcases List.mem_cons.1 hc with rfl | hcTail
      · exact ihHead
      · exact ihTail c hcTail
  exact hP h5

theorem renderRows_bfsAssign_All_WF (z α a b c : K)
    (t : NTree (GenComputeRow K)) (hz : z ≠ 0)
    (h5 : NTree.All (fun g => rlc5Holds a b c (renderNode z α g).row.2.2.1)
      (bfsAssign t)) :
    NTree.All (fun g => WF (challengeInputs z α a b c) g.row.2.2.1)
      (renderRows z α (bfsAssign t)) :=
  renderRows_All_WF z α a b c (bfsAssign t) hz h5

/-! ## Leaf `WF` after BFS assign + render -/

theorem renderRows_bfsAssign_leaf_WF (z α a b c : K) (g : GenComputeRow K)
    (hz : z ≠ 0)
    (h5 : rlc5Holds a b c
      (renderNode z α (bfsAssign (.node g [])).label).row.2.2.1) :
    WF (challengeInputs z α a b c)
      (renderRows z α (bfsAssign (.node g []))).label.row.2.2.1 := by
  rw [renderRows_label_row]
  exact renderNode_WF z α a b c (bfsAssign (.node g [])).label hz h5

theorem renderRows_bfsAssign_op8_leaf_WF (z α a b c : K) (g : GenComputeRow K)
    (hz : z ≠ 0) (hstate : g.skel.state = State.s8) :
    WF (challengeInputs z α a b c)
      (renderRows z α (bfsAssign (.node g []))).label.row.2.2.1 := by
  refine renderRows_bfsAssign_leaf_WF z α a b c g hz ?_
  have hne : (bfsAssign (.node g [])).label.skel.state ≠ State.s5 := by
    rw [bfsAssign_leaf_label, hstate]
    intro h; cases h
  exact renderNode_rlc5Holds_of_ne_s5 z α a b c _ hne

theorem renderRows_bfsAssign_cons_leaf_WF (z α a b c : K) (g : GenComputeRow K)
    (hz : z ≠ 0) (hstate : g.skel.state = State.cons) :
    WF (challengeInputs z α a b c)
      (renderRows z α (bfsAssign (.node g []))).label.row.2.2.1 := by
  refine renderRows_bfsAssign_leaf_WF z α a b c g hz ?_
  have hne : (bfsAssign (.node g [])).label.skel.state ≠ State.s5 := by
    rw [bfsAssign_leaf_label, hstate]
    intro h; cases h
  exact renderNode_rlc5Holds_of_ne_s5 z α a b c _ hne

/-! ## `OP_5` RLC coins -/

/-- Leaf coin `c = 1` separates unequal atom encodings and is vacuous on
    equal operands. -/
theorem rlc5Holds_c_one_of_atom_or_eq (z : K) (pub : Pub K) {u v : Noun}
    (h1 : pub.sf1_e = encC z u) (h2 : pub.sf2_e = encC z v)
    (h : u = v ∨ ∃ a b : ℕ, u = .atom a ∧ v = .atom b) :
    rlc5Holds (0 : K) 0 1 pub := by
  intro hn
  rcases h with heq | ⟨a, b, ha, hb⟩
  · subst heq
    exact (hn.2 (h1.trans h2.symm)).elim
  · have hform : rlc5Form (0 : K) 0 1 pub = pub.sf1_e.leaf - pub.sf2_e.leaf := by
      simp [rlc5Form, deltaSize, deltaDyck, deltaLeaf]
    have hleaf : pub.sf1_e.leaf - pub.sf2_e.leaf = (a : K) - (b : K) := by
      rw [h1, h2, ha, hb]
      simp [encC_eq, GlobalCarryRecognizer.enc_atom, FP.atomFP]
    rw [hform, hleaf]
    intro hz
    have hcast : (a : K) = (b : K) := sub_eq_zero.mp hz
    have henc : encC z u = encC z v := by
      rw [ha, hb]
      simp [encC_eq, GlobalCarryRecognizer.enc_atom, FP.atomFP, hcast]
    exact hn.2 (h1.trans (henc.trans h2.symm))

theorem renderOp5Row_rlc5_c_one_of_atom_or_eq (z α : K)
    (stamp : ComputeTimestampRow) (skel : ComputeRowSkeleton)
    (h : P8Census.skeletonSubformula skel 0 TripleSlot.result =
        P8Census.skeletonSubformula skel 1 TripleSlot.result ∨
      ∃ a b : ℕ,
        P8Census.skeletonSubformula skel 0 TripleSlot.result = .atom a ∧
          P8Census.skeletonSubformula skel 1 TripleSlot.result = .atom b) :
    rlc5Holds (0 : K) 0 1 (renderOp5Row z α stamp skel).2.2.1 :=
  rlc5Holds_c_one_of_atom_or_eq z (renderOp5Row z α stamp skel).2.2.1
    (by simp [renderOp5Row]) (by simp [renderOp5Row]) h

theorem renderNode_rlc5Holds_c_one (z α : K) (g : GenComputeRow K)
    (h : g.skel.state = State.s5 →
      P8Census.skeletonSubformula g.skel 0 TripleSlot.result =
          P8Census.skeletonSubformula g.skel 1 TripleSlot.result ∨
        ∃ a b : ℕ,
          P8Census.skeletonSubformula g.skel 0 TripleSlot.result = .atom a ∧
            P8Census.skeletonSubformula g.skel 1 TripleSlot.result = .atom b) :
    rlc5Holds (0 : K) 0 1 (renderNode z α g).row.2.2.1 := by
  by_cases hs : g.skel.state = State.s5
  · rw [renderNode_op5_row z α g hs]
    exact renderOp5Row_rlc5_c_one_of_atom_or_eq z α g.stamp g.skel (h hs)
  · exact renderNode_rlc5Holds_of_ne_s5 z α 0 0 1 g hs

theorem renderNode_WF_c_one (z α : K) (g : GenComputeRow K) (hz : z ≠ 0)
    (h : g.skel.state = State.s5 →
      P8Census.skeletonSubformula g.skel 0 TripleSlot.result =
          P8Census.skeletonSubformula g.skel 1 TripleSlot.result ∨
        ∃ a b : ℕ,
          P8Census.skeletonSubformula g.skel 0 TripleSlot.result = .atom a ∧
            P8Census.skeletonSubformula g.skel 1 TripleSlot.result = .atom b) :
    WF (challengeInputs z α 0 0 1) (renderNode z α g).row.2.2.1 :=
  renderNode_WF z α 0 0 1 g hz (renderNode_rlc5Holds_c_one z α g h)

theorem renderOp5Row_rlc5_c_one (z α : K) (stamp : ComputeTimestampRow)
    (skel : ComputeRowSkeleton)
    (hsf1 : P8Census.skeletonSubformula skel 0 .result = Noun.atom 3)
    (hsf2 : P8Census.skeletonSubformula skel 1 .result = Noun.atom 4) :
    rlc5Holds (0 : K) 0 1 (renderOp5Row z α stamp skel).2.2.1 := by
  intro _ hf
  have hform :
      rlc5Form (0 : K) 0 1 (renderOp5Row z α stamp skel).2.2.1 =
        (encC z (P8Census.skeletonSubformula skel 0 .result)).leaf -
          (encC z (P8Census.skeletonSubformula skel 1 .result)).leaf := by
    simp [rlc5Form, deltaSize, deltaDyck, deltaLeaf, renderOp5Row]
  rw [hform, hsf1, hsf2, encC_eq, encC_eq, GlobalCarryRecognizer.enc_atom,
    GlobalCarryRecognizer.enc_atom] at hf
  simp [FP.atomFP] at hf
  have hdiff : (3 : K) - 4 = -1 := by ring
  have hneg : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  exact hneg (hdiff ▸ hf)

theorem renderRows_bfsAssign_op5_leaf_WF_c_one (z α : K) (g : GenComputeRow K)
    (hz : z ≠ 0) (hstate : g.skel.state = State.s5)
    (hsf1 : P8Census.skeletonSubformula g.skel 0 .result = Noun.atom 3)
    (hsf2 : P8Census.skeletonSubformula g.skel 1 .result = Noun.atom 4) :
    WF (challengeInputs z α 0 0 1)
      (renderRows z α (bfsAssign (.node g []))).label.row.2.2.1 := by
  refine renderRows_bfsAssign_leaf_WF z α 0 0 1 g hz ?_
  have hstate' : (bfsAssign (.node g [])).label.skel.state = State.s5 := by
    simpa [bfsAssign_leaf_label] using hstate
  have hsf1' : P8Census.skeletonSubformula (bfsAssign (.node g [])).label.skel 0
      .result = Noun.atom 3 := by
    simpa [bfsAssign_leaf_label] using hsf1
  have hsf2' : P8Census.skeletonSubformula (bfsAssign (.node g [])).label.skel 1
      .result = Noun.atom 4 := by
    simpa [bfsAssign_leaf_label] using hsf2
  rw [renderNode_op5_row z α _ hstate']
  exact renderOp5Row_rlc5_c_one z α _ _ hsf1' hsf2'

/-! ## Non-vacuity witnesses -/

theorem renderRows_bfsAssign_op8_leaf_WF_nonvacuous (z α a b c : K)
    (hz : z ≠ 0) :
    let g : GenComputeRow K :=
      { skel := op8EvalVSkel
        stamp := stampOfAcc State.s8 0
        row := renderOp8Row z α (stampOfAcc State.s8 0) op8EvalVSkel
        requests := [] }
    WF (challengeInputs z α a b c)
      (renderRows z α (bfsAssign (.node g []))).label.row.2.2.1 :=
  renderRows_bfsAssign_op8_leaf_WF z α a b c
    { skel := op8EvalVSkel
      stamp := stampOfAcc State.s8 0
      row := renderOp8Row z α (stampOfAcc State.s8 0) op8EvalVSkel
      requests := [] } hz rfl

def consSizeSkel : ComputeRowSkeleton where
  state := .cons
  subject := Noun.atom 0
  formula := Noun.cell (Noun.cell (Noun.atom 1) (Noun.atom 3))
    (Noun.cell (Noun.atom 1) (Noun.atom 4))
  evaluation := Noun.cell (Noun.atom 3) (Noun.atom 4)
  decomposition := fun _ _ => Noun.atom 0
  subformula := fun _ _ _ => Noun.atom 0
  memoryRecord := fun _ _ => ⟨Noun.atom 0, Noun.atom 0, 3⟩

theorem renderRows_bfsAssign_cons_leaf_WF_nonvacuous (z α a b c : K)
    (hz : z ≠ 0) :
    let g : GenComputeRow K :=
      { skel := consSizeSkel
        stamp := stampOfAcc State.cons 0
        row := renderConsRow z α (stampOfAcc State.cons 0) consSizeSkel
        requests := [] }
    WF (challengeInputs z α a b c)
      (renderRows z α (bfsAssign (.node g []))).label.row.2.2.1 :=
  renderRows_bfsAssign_cons_leaf_WF z α a b c
    { skel := consSizeSkel
      stamp := stampOfAcc State.cons 0
      row := renderConsRow z α (stampOfAcc State.cons 0) consSizeSkel
      requests := [] } hz rfl

theorem renderRows_bfsAssign_op5_leaf_WF_nonvacuous (z α : K)
    (hz : z ≠ 0) :
    let g : GenComputeRow K :=
      { skel := op5VcompSkel
        stamp := stampOfAcc State.s5 0
        row := renderOp5Row z α (stampOfAcc State.s5 0) op5VcompSkel
        requests := [] }
    WF (challengeInputs z α 0 0 1)
      (renderRows z α (bfsAssign (.node g []))).label.row.2.2.1 := by
  refine renderRows_bfsAssign_op5_leaf_WF_c_one z α
    { skel := op5VcompSkel
      stamp := stampOfAcc State.s5 0
      row := renderOp5Row z α (stampOfAcc State.s5 0) op5VcompSkel
      requests := [] } hz rfl ?hsf1 ?hsf2
  · simp [op5VcompSkel, genSkelOp5, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [op5VcompSkel, genSkelOp5, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]

/-! ## Counting: good `rlc5` coins exist when `N < |K|` -/

open Classical

theorem exists_rlc5_coins [Fintype K] [DecidableEq K] {n : ℕ}
    (rows : Fin n → Pub K)
    (hn : n < Fintype.card K) :
    ∃ coins : ComputeCoins K,
      ∀ i, rlc5Holds coins.1 coins.2.1 coins.2.2 (rows i) := by
  have hcard :
      n * (Fintype.card K * Fintype.card K) < Fintype.card K ^ 3 := by
    have hpos : 0 < Fintype.card K * Fintype.card K :=
      Nat.mul_pos Fintype.card_pos Fintype.card_pos
    have hmul := Nat.mul_lt_mul_of_pos_right hn hpos
    simpa [pow_three, mul_assoc] using hmul
  have hle := badComputeAny_card_le rows
  have hlt : (badComputeAny rows).card < Fintype.card (ComputeCoins K) := by
    rw [card_computeCoins]
    exact lt_of_le_of_lt hle hcard
  have hne : badComputeAny rows ≠ Finset.univ := by
    intro hEq
    rw [hEq, Finset.card_univ] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨coins, -, hmem⟩ :=
    Finset.exists_of_ssubset (Finset.ssubset_univ_iff.mpr hne)
  exact ⟨coins, (rlc5All_iff_not_mem_badAny coins rows).mpr hmem⟩

/-! ## I/O coin-genericity, same counting pattern -/

open Nock.NockVMROM.Thm54.FiniteIO

/-- Split `∉ IOFailureEvent` into the three named Inputs fields.  Abstract in the
    table field so K3 decidability never unfolds. -/
theorem not_mem_ioFailure_components {L : Type*} [Field L] [Fintype L]
    [DecidableEq L] {n : ℕ}
    {records : PreChallengeRecords L n} {γ p : L}
    (h : (γ, p) ∉ IOFailureEvent records) :
    p ∉ IOPoleHitEvent records γ ∧
      γ ∉ IORLCCollisionEvent records ∧
      p ∉ IOLogDerivEvent records γ := by
  simp only [IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    not_or] at h
  exact ⟨h.2.1, h.1, h.2.2⟩

theorem exists_io_coins {L : Type*} [Field L] [Fintype L] [DecidableEq L]
    {n : ℕ} (records : PreChallengeRecords L n)
    (hcard : (IOFailureEvent records).card < Fintype.card (L × L)) :
    ∃ coins : IOCoins L, (coins.gamma, coins.pole) ∉ IOFailureEvent records := by
  have hne : IOFailureEvent records ≠ Finset.univ := by
    intro hEq
    rw [hEq, Finset.card_univ] at hcard
    exact lt_irrefl _ hcard
  obtain ⟨q, -, hq⟩ := Finset.exists_of_ssubset (Finset.ssubset_univ_iff.mpr hne)
  exact ⟨⟨q.1, q.2⟩, hq⟩

theorem ioFailureBound_of_lengths {L : Type*} [Field L] [Fintype L]
    [DecidableEq L] {n k₁ k₂ : ℕ} (records : PreChallengeRecords L n)
    (hr : records.requests.length = k₁) (hs : records.responses.length = k₂)
    (hcard : ioFailureUnionBound n k₁ k₂ (Fintype.card L) <
      Fintype.card (L × L)) :
    (IOFailureEvent records).card < Fintype.card (L × L) := by
  refine lt_of_le_of_lt (IOFailureEvent_card_le records) ?_
  rw [hr, hs]
  exact hcard

end Nock.NockVMROM.Thm54.TraceGen

/-! ## Over `K3` (`|K| = 97³`) -/

namespace Nock.NockVMROM.Thm54.TraceGen.CubicField97
namespace K3

open Nock.NockVMROM.Thm54.TraceGen
open Nock.TableWFBounds
open Nock.NockVMROM.Thm54.FiniteIO
open Classical

set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false

noncomputable section

/-- Good `(a,b,c)` exist for any `n < 97³` rendered pubs over `K3`. -/
theorem exists_rlc5_coins_K3 {n : ℕ} (rows : Fin n → ComputeTable.Pub K3)
    (hn : n < 97 ^ 3) :
    ∃ coins : ComputeCoins K3,
      ∀ i, rlc5Holds coins.1 coins.2.1 coins.2.2 (rows i) := by
  have hn' : n < Fintype.card K3 := by simpa [card_eq] using hn
  exact exists_rlc5_coins (K := K3) rows hn'

/-- Empty pre-challenge records: union bound is `0`, so every coin pair is good. -/
def emptyRecords8 : PreChallengeRecords K3 8 := ⟨[], []⟩

theorem emptyRecords8_lengths :
    emptyRecords8.requests.length = 0 ∧ emptyRecords8.responses.length = 0 :=
  ⟨rfl, rfl⟩

theorem ioFailureBound_empty_K3 :
    (IOFailureEvent emptyRecords8).card < Fintype.card (K3 × K3) :=
  ioFailureBound_of_lengths emptyRecords8 emptyRecords8_lengths.1
    emptyRecords8_lengths.2
    (by
      rw [ioFailureUnionBound, Fintype.card_prod,
        show Fintype.card K3 = 97 ^ 3 from card_eq]
      norm_num)

theorem goodIOCoinsK3_exists :
    ∃ coins : IOCoins K3,
      (coins.gamma, coins.pole) ∉ IOFailureEvent emptyRecords8 :=
  exists_io_coins emptyRecords8 ioFailureBound_empty_K3

def ioCoinsK3 : IOCoins K3 := Classical.choose goodIOCoinsK3_exists

theorem ioCoinsK3_good :
    (ioCoinsK3.gamma, ioCoinsK3.pole) ∉ IOFailureEvent emptyRecords8 :=
  Classical.choose_spec goodIOCoinsK3_exists

/-- `ioPoleHitGood` for the empty-record K3 witness. -/
theorem ioCoinsK3_poleHitGood :
    ioCoinsK3.pole ∉ IOPoleHitEvent emptyRecords8 ioCoinsK3.gamma :=
  (not_mem_ioFailure_components ioCoinsK3_good).1

/-- `ioGammaGood` for the empty-record K3 witness. -/
theorem ioCoinsK3_gammaGood :
    ioCoinsK3.gamma ∉ IORLCCollisionEvent emptyRecords8 :=
  (not_mem_ioFailure_components ioCoinsK3_good).2.1

/-- `ioLogDerivGood` for the empty-record K3 witness. -/
theorem ioCoinsK3_logDerivGood :
    ioCoinsK3.pole ∉ IOLogDerivEvent emptyRecords8 ioCoinsK3.gamma :=
  (not_mem_ioFailure_components ioCoinsK3_good).2.2

end

end K3
end Nock.NockVMROM.Thm54.TraceGen.CubicField97

#print axioms Nock.NockVMROM.Thm54.TraceGen.renderOp8Row_sizes
#print axioms Nock.NockVMROM.Thm54.TraceGen.renderConsRow_sizes
#print axioms Nock.NockVMROM.Thm54.TraceGen.renderNode_WF
#print axioms Nock.NockVMROM.Thm54.TraceGen.renderRows_bfsAssign_All_WF
#print axioms Nock.NockVMROM.Thm54.TraceGen.renderRows_bfsAssign_op8_leaf_WF_nonvacuous
#print axioms Nock.NockVMROM.Thm54.TraceGen.renderRows_bfsAssign_cons_leaf_WF_nonvacuous
#print axioms Nock.NockVMROM.Thm54.TraceGen.renderRows_bfsAssign_op5_leaf_WF_nonvacuous
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_rlc5_coins
#print axioms Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.exists_rlc5_coins_K3
#print axioms Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.ioCoinsK3_poleHitGood
#print axioms Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.ioCoinsK3_gammaGood
#print axioms Nock.NockVMROM.Thm54.TraceGen.CubicField97.K3.ioCoinsK3_logDerivGood
