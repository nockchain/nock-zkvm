/-
  Nock/NockVMROM/Thm54/P8Core/RootGoodFJoin.lean

* `CtxW z q W D t S0 F0` — the context: `Batch1171.Ctx` with `G` / `hΛG` deleted, the served-record
    and census oracles at the field join, and the window as an explicit parameter `W` with three
    abstract premises: `hW1 : 1 ≤ W`, `hlow : LowOrderFree z W` and **`calls`**: every call at depth
    `< D` of the field call tree `CallTreeF q S0 F0` of the claim has inputs and field result with
    `≤ W` leaves (`hD : t.size ≤ D`).  `calls` is a function of `(q, S0, F0, D, W)` only, not of the
    prover.
  * `InpW` — the per-node inputs: `Batch1171.Inp` with `HonestCall G s f` replaced by the
    **`callTreeF`-prefix invariant** `∃ d, d + u.size ≤ t.size ∧ CallTreeF q S0 F0 d s f`, and the
    guarded run deleted.  The node's window is DERIVED from `calls` (`InpW.win`, `InpW.evalWin`).
  * the twelve step lemmas `step_*W` and the induction `good_of_inpW`, then **`root_goodF`**.

  What replaces the honest data, arm by arm (the probe R1's table, extended):
  * shapes (formula a cell, tails cells, OP0 tail / OP9 axis atoms): the served records 0/1/2 and the
    `size = z` gates with `LowOrderFree`;

  * kid evaluations (`kid_eval*` ×21): the kid's field run (`kidRun`) — windowed by `calls`, bounded by
    `SVInductionGenericF.kid_eval_boundedF`;
  * OP4's atom operand and OP6's `0/1` selector: the chip's own gates (`evalV`: `sf1_e.size = z`,
    `sf2_e.size = z`, `sf2_e.leaf ∈ {0, 1}`) with `LowOrderFree` and `hcast`.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.RootGoodF
import Nock.NockVMROM.Thm54.P8Core.Batch1515Thm54SVInductionGenericF

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

namespace Nock.NockVMROM.Thm54.RootGoodFJoin

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.SVJoinF
open Nock.NockVMROM.Thm54.SVJoinAssemblyF
open Nock.NockVMROM.Thm54.SVReadyFuelF
open Nock.NockVMROM.Thm54.SVGenuineF
open Nock.NockVMROM.Thm54.SVAlignmentF
open Nock.NockVMROM.Thm54.SVInductionGenericF
open Nock.NockVMROM.Thm54.ComputedWindow
open Nock.NockVMROM.Thm54.RootGoodF
open Nock.RedTeam
open Nock.GlobalCarryRecognizer
open Nock.FieldEmbedding

variable {K : Type} [Field K] [DecidableEq K] [Fintype K] [CharP K (ringChar K)]
variable {sv : MState → ℕ → Noun} {ax : ℕ → ℕ}
set_option quotPrecheck false
set_option hygiene false in
local notation "J" => c2JoinFuelF q (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) sv ax

/-! ## §A  The context, the inputs, the outputs -/

/-- **The window premise over the field call tree** (the entry point L-C prices): every call at
depth `< D` of `CallTreeF q S0 F0` has inputs and field result with `≤ W` leaves. -/
def CallsWithin (q : ℕ) (S0 F0 : Noun) (D W : ℕ) : Prop :=
  ∀ d s f, d < D → CallTreeF q S0 F0 d s f →
    s.leaves ≤ W ∧ f.leaves ≤ W ∧ ∀ n r, evalFBy q n s f = some r → r.leaves ≤ W

/-- **The package-free context at the field join.** -/
structure CtxW (z : K) (q W D : ℕ) (t : NTree ((State × DTcomp K) × ℕ)) (S0 F0 : Noun) : Prop where
  hz : z ≠ 0
  hq12 : 12 ≤ q
  hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q)
  hW1 : 1 ≤ W
  hlow : LowOrderFree z W
  hD : t.size ≤ D
  calls : CallsWithin q S0 F0 D W
  row : ∀ u, InTree t u → Batch1171.RowFacts (ax := ax) z q u
  recs : ∀ u s f, Batch1171.PR t (J t.size t S0 F0) u (J u.size u s f) →
    Batch1171.RecOK z q W u.label (J u.size u s f).label
  census : ∀ u s f, InTree t u → InTree (J t.size t S0 F0) (J u.size u s f) →
    Batch1171.CensusOK z W (J u.size u s f).label

/-- **The inputs at a node**: reached, positionally reached, a prefix call of the claim's field call
tree at a depth leaving room for the subtree, bounded inputs, the two input bindings. -/
structure InpW (z : K) (q : ℕ) (t : NTree ((State × DTcomp K) × ℕ)) (S0 F0 : Noun)
    (u : NTree ((State × DTcomp K) × ℕ)) (s f : Noun) : Prop where
  inT : InTree t u
  reach : InTree (J t.size t S0 F0) (J u.size u s f)
  pr : Batch1171.PR t (J t.size t S0 F0) u (J u.size u s f)
  call : ∃ d, d + u.size ≤ t.size ∧ CallTreeF q S0 F0 d s f
  bs : BoundedBy q s
  bf : BoundedBy q f
  hs : bindFP z s u.label.1.2.2.1.s
  hf : bindFP z f u.label.1.2.2.1.f

/-- **The outputs at a node**: field chip readiness and field alignment. -/
def GoodW (z : K) (q : ℕ) (u : NTree ((State × DTcomp K) × ℕ)) (s f : Noun) : Prop :=
  C2ChipReady (sv := sv) (ax := ax) z q u s f ∧ C2Aligned (sv := sv) (ax := ax) q u s f

section Basics

variable {z : K} {q W D : ℕ} {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}

theorem CtxW.hq (C : CtxW (sv := sv) (ax := ax) z q W D t S0 F0) : 1 < q := by
  have := C.hq12; omega

/-- The node's window, from the call-tree invariant. -/
theorem InpW.callWin (C : CtxW (sv := sv) (ax := ax) z q W D t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : InpW (sv := sv) (ax := ax) z q t S0 F0 u s f) :
    s.leaves ≤ W ∧ f.leaves ≤ W ∧ ∀ n r, evalFBy q n s f = some r → r.leaves ≤ W := by
  obtain ⟨d, hd, hc⟩ := I.call
  have := Batch1021.ntree_size_pos u
  exact C.calls d s f (by have := C.hD; omega) hc

theorem InpW.win (C : CtxW (sv := sv) (ax := ax) z q W D t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : InpW (sv := sv) (ax := ax) z q t S0 F0 u s f) : s.leaves ≤ W ∧ f.leaves ≤ W :=
  ⟨(I.callWin C).1, (I.callWin C).2.1⟩

/-- A child's call: one level deeper, with room for the child's subtree. -/
theorem InpW.childCall {u c : NTree ((State × DTcomp K) × ℕ)} {s f s' f' : Noun}
    (I : InpW (sv := sv) (ax := ax) z q t S0 F0 u s f) (hc : c.size + 1 ≤ u.size)
    (step : ∀ d, CallTreeF q S0 F0 d s f → CallTreeF q S0 F0 (d + 1) s' f') :
    ∃ d, d + c.size ≤ t.size ∧ CallTreeF q S0 F0 d s' f' := by
  obtain ⟨d, hd, hcl⟩ := I.call
  exact ⟨d + 1, by omega, step d hcl⟩

/-- A good kid's field root evaluation is a field run of its inputs. -/
theorem kidRun {c : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (hG : GoodW (sv := sv) (ax := ax) z q c s f) :
    ∃ n, evalFBy q n s f = some (J c.size c s f).label.evaluation := by
  have hg := genuineF_of_ready (z := z) hG.2 c.size le_rfl hG.1
  exact ⟨_, by simpa [J_subject', J_formula'] using genuineF_evalFBy hg⟩

/-- A good kid's evaluation is windowed by the call-tree premise. -/
theorem kidWin (C : CtxW (sv := sv) (ax := ax) z q W D t S0 F0)
    {c : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : InpW (sv := sv) (ax := ax) z q t S0 F0 c s f)
    (hG : GoodW (sv := sv) (ax := ax) z q c s f) :
    (J c.size c s f).label.evaluation.leaves ≤ W := by
  obtain ⟨n, hn⟩ := kidRun hG
  exact (I.callWin C).2.2 n _ hn

/-- A good kid's evaluation is over 𝔽 when its inputs are. -/
theorem kidBounded (C : CtxW (sv := sv) (ax := ax) z q W D t S0 F0)
    {c : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (hG : GoodW (sv := sv) (ax := ax) z q c s f) (bs : BoundedBy q s) (bf : BoundedBy q f) :
    BoundedBy q (J c.size c s f).label.evaluation :=
  kid_eval_boundedF C.hq (genuineF_of_ready (z := z) hG.2 c.size le_rfl hG.1) bs bf

end Basics

/-! ## §B  Run-free shape facts at the field join -/

section Shapes

variable {z : K} {q W D : ℕ} {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}

theorem skeletonDec_fhF (st : State) (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    P8Census.skeletonDec (c2SkeletonRowF q sv ax st S s f kids) .f_h = nounHead f := by
  simp [P8Census.skeletonDec, c2SkeletonRowF, decActive]

theorem opcodeHead_memF (st : State) (hst : st ≠ .cons) (S : ℕ) (s f : Noun)
    (kids : List ComputeRowSkeleton) :
    P8Census.skeletonUse .opcodeHead (nounHead f) (.atom st.toNat) ∈
      P8Census.skeletonComparisons (K := K) (c2SkeletonRowF q sv ax st S s f kids) := by
  have hd := skeletonDec_fhF (q := q) (sv := sv) (ax := ax) st S s f kids
  cases st <;> simp [P8Census.skeletonComparisons, c2SkeletonRowF, State.toNat] at hd hst ⊢ <;>
    simp [hd]

/-- Record 0 at the field join: the formula is a cell, `enc b = f_t`, `enc a = f_h`. -/
theorem slot0W (C : CtxW (sv := sv) (ax := ax) z q W D t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : InpW (sv := sv) (ax := ax) z q t S0 F0 u s f) :
    ∃ a b, f = .cell a b ∧ bindFP z b u.label.1.2.2.2.f_t ∧ bindFP z a u.label.1.2.2.2.f_h := by
  have R := C.row u I.inT
  have hV := R.vcomp
  have hrec := C.recs u s _ I.pr
  have hj : ((0 : Fin 3) : ℕ) < Nock.Framework.recordCount (J u.size u s f).label.state :=
    Batch1171.recordCount_pos' _
  have hmr1 : Batch1171.traceRec u.label 0 = ⟨u.label.1.2.2.1.f, u.label.1.2.2.2.f_t, 3,
      u.label.1.2.2.1.ln_prev * u.label.1.2.1.α⟩ := hV.2.1
  have h := hrec 0 hj
  rw [J_rec] at h
  simp only [Fin.val_zero] at h
  rw [c2RecF_0, hmr1] at h
  obtain ⟨hslot, hb⟩ := h (Batch1171.enc_eq_of_bind I.hf) (I.win C).2 I.bf
  cases f with
  | atom k => simp [Noun.slot] at hslot
  | cell a b =>
  simp only [nounTail] at hb
  have hbt : bindFP z b u.label.1.2.2.2.f_t := hb.symm
  refine ⟨a, b, rfl, hbt, ?_⟩
  have hcons : FP.cons z (enc z a) u.label.1.2.2.2.f_t =
      FP.cons z u.label.1.2.2.2.f_h u.label.1.2.2.2.f_t := by
    have h1 : enc z (Noun.cell a b) = u.label.1.2.2.1.f := Batch1171.enc_eq_of_bind I.hf
    rw [enc_cons C.hz, ← hbt] at h1
    rw [h1, hV.1, R.zRow]
  have hne : u.label.1.2.2.2.f_t.size ≠ 0 := by rw [hbt]; exact Batch1171.enc_size_ne_zero C.hz b
  exact (Batch1023.cons_left_cancel C.hz hne hcons).symm

/-- The head at a non-`cons` row is the opcode atom (census separation + `SVhead`). -/
theorem head_atomW (C : CtxW (sv := sv) (ax := ax) z q W D t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} {s a b : Noun}
    (I : InpW (sv := sv) (ax := ax) z q t S0 F0 u s (.cell a b))
    (hcons : u.label.1.1 ≠ .cons) (ha : bindFP z a u.label.1.2.2.2.f_h) :
    a = .atom u.label.1.1.toNat := by
  have R := C.row u I.inT
  have hV := R.vcomp
  have hpc : u.label.1.2.2.1.state ≠ State.cons := by rw [R.pubSt]; exact hcons
  have hst' : u.label.1.2.2.1.state.toNat = u.label.1.1.toNat := by rw [R.pubSt]
  have hfh : u.label.1.2.2.2.f_h = FP.atomFP u.label.1.2.1.z (u.label.1.1.toNat : K) :=
    @Batch1021.vcomp_f_h_eq_atomFP K _ _ _ _ _ _ _ hV _ hst' hpc
  have henc : enc z a = enc z (.atom u.label.1.1.toNat) := by
    rw [enc_atom, ← ha, hfh, R.zRow]
  have hcen := C.census u s _ I.inT I.reach
  have hmem : P8Census.skeletonUse .opcodeHead a (.atom u.label.1.1.toNat) ∈
      P8Census.skeletonComparisons (K := K) (J u.size u s (.cell a b)).label := by
    rw [J_label_eq]
    have := opcodeHead_memF (K := K) (q := q) (sv := sv) (ax := ax) u.label.1.1 hcons u.label.2 s
      (.cell a b) ((J u.size u s (.cell a b)).children.map NTree.label)
    simpa [nounHead] using this
  have hsep := hcen _ hmem (by show a.leaves ≤ W; exact (Batch1171.leaves_head_le a b).trans (I.win C).2)
    (by show (Noun.atom _).leaves ≤ W; rw [Batch1171.leaves_atom]; exact C.hW1)
  have hop : u.label.1.1.toNat < q := by
    have : u.label.1.1.toNat ≤ 9 := by cases u.label.1.1 <;> decide
    have := C.hq12
    omega
  exact noun_eq_of_enc_eq z a _ hsep C.hcast I.bf.1 (by simpa using hop) henc

/-- The head at a `cons` row is a cell (`SVhead`'s `headCell`). -/
theorem head_cellW (C : CtxW (sv := sv) (ax := ax) z q W D t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} {s a b : Noun}
    (I : InpW (sv := sv) (ax := ax) z q t S0 F0 u s (.cell a b))
    (hcons : u.label.1.1 = .cons) (ha : bindFP z a u.label.1.2.2.2.f_h) :
    ∃ lh lt, a = .cell lh lt := by
  have R := C.row u I.inT
  have hV := R.vcomp
  have hsv : SVhead u.label.1.2.1 u.label.1.2.2.1 u.label.1.2.2.2 := hV.2.2.1
  have hpc : u.label.1.2.2.1.state = State.cons := by rw [R.pubSt]; exact hcons
  simp only [SVhead, hpc, if_true, headCell] at hsv
  cases a with
  | atom k =>
      exfalso
      apply hsv
      rw [ha, enc_atom]
      rfl
  | cell lh lt => exact ⟨lh, lt, rfl⟩

/-- Record `j ∈ {1, 2}` at a served position: the record's root slot exists and its child binds. -/
theorem recW (C : CtxW (sv := sv) (ax := ax) z q W D t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : InpW (sv := sv) (ax := ax) z q t S0 F0 u s f) (j : Fin 3)
    (hj : (j : ℕ) < Nock.Framework.recordCount u.label.1.1) {root child : Noun} {axis : ℕ}
    (hrecj : c2RecF sv ax u.label.1.1 u.label.2 s f
      ((J u.size u s f).children.map NTree.label) j = ⟨root, child, axis⟩)
    (hroot : enc z root = (Batch1171.traceRec u.label j).root) (hL : root.leaves ≤ W)
    (hb : BoundedBy q root) :
    Noun.slot axis root = some child ∧ enc z child = (Batch1171.traceRec u.label j).child := by
  have hrec := C.recs u s _ I.pr
  have h := hrec j (by rw [J_label_eq]; exact hj)
  rw [J_rec, hrecj] at h
  exact h hroot hL hb

/-- Record 1 at a two-record row: `b = [c d]`, `enc c = f_th`, `enc d = f_tt` (no run). -/
theorem tail_bind2W (C : CtxW (sv := sv) (ax := ax) z q W D t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} {s a b : Noun}
    (I : InpW (sv := sv) (ax := ax) z q t S0 F0 u s (.cell a b))
    (hb : bindFP z b u.label.1.2.2.2.f_t)
    (h1 : (1 : ℕ) < Nock.Framework.recordCount u.label.1.1)
    (hrec1 : c2RecF sv ax u.label.1.1 u.label.2 s (.cell a b)
      ((J u.size u s (.cell a b)).children.map NTree.label) 1 = ⟨b, nounHead b, 2⟩)
    (hmr2 : ∃ ts, u.label.1.2.2.1.mr2 = ⟨u.label.1.2.2.2.f_t, u.label.1.2.2.2.f_th, 2, ts⟩)
    (hcons : FP.cons z u.label.1.2.2.2.f_th u.label.1.2.2.2.f_tt = u.label.1.2.2.2.f_t) :
    ∃ c d, b = .cell c d ∧ bindFP z c u.label.1.2.2.2.f_th ∧ bindFP z d u.label.1.2.2.2.f_tt := by
  obtain ⟨ts, hmr2⟩ := hmr2
  have hmr : Batch1171.traceRec u.label 1 = u.label.1.2.2.1.mr2 := rfl
  obtain ⟨hslot, hc⟩ := recW C I 1 h1 hrec1 (by show enc z b = u.label.1.2.2.1.mr2.root; rw [hmr2]; exact Batch1171.enc_eq_of_bind hb)
    ((Batch1171.leaves_tail_le a _).trans (I.win C).2) I.bf.2
  cases b with
  | atom k => simp [Noun.slot] at hslot
  | cell c d =>
  change enc z (nounHead (Noun.cell c d)) = u.label.1.2.2.1.mr2.child at hc
  rw [hmr2] at hc
  simp only [nounHead] at hc
  have hcb : bindFP z c u.label.1.2.2.2.f_th := hc.symm
  refine ⟨c, d, rfl, hcb, ?_⟩
  have hcc : FP.cons z u.label.1.2.2.2.f_th (enc z d) =
      FP.cons z u.label.1.2.2.2.f_th u.label.1.2.2.2.f_tt := by
    have := Batch1171.enc_eq_of_bind hb
    rw [enc_cons C.hz, ← hcb] at this
    rw [hcons]
    exact this
  have hne : u.label.1.2.2.2.f_th.size ≠ 0 := by rw [hcb]; exact Batch1171.enc_size_ne_zero C.hz c
  exact (Batch758.cons_right_cancel hne hcc).symm

/-- Record 2 at an OP6 row: `d = [e g]`, `enc e = f_tth`, `enc g = f_ttt` (no run). -/
theorem tail_bind3W (C : CtxW (sv := sv) (ax := ax) z q W D t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} {s a c d : Noun}
    (I : InpW (sv := sv) (ax := ax) z q t S0 F0 u s (.cell a (.cell c d)))
    (hd : bindFP z d u.label.1.2.2.2.f_tt)
    (h2 : (2 : ℕ) < Nock.Framework.recordCount u.label.1.1)
    (hrec2 : c2RecF sv ax u.label.1.1 u.label.2 s (.cell a (.cell c d))
      ((J u.size u s (.cell a (.cell c d))).children.map NTree.label) 2 = ⟨d, nounHead d, 2⟩)
    (hmr3 : ∃ ts, u.label.1.2.2.1.mr3 = ⟨u.label.1.2.2.2.f_tt, u.label.1.2.2.2.f_tth, 2, ts⟩)
    (hcons : FP.cons z u.label.1.2.2.2.f_tth u.label.1.2.2.2.f_ttt = u.label.1.2.2.2.f_tt) :
    ∃ e g, d = .cell e g ∧ bindFP z e u.label.1.2.2.2.f_tth ∧ bindFP z g u.label.1.2.2.2.f_ttt := by
  obtain ⟨ts, hmr3⟩ := hmr3
  have hmr : Batch1171.traceRec u.label 2 = u.label.1.2.2.1.mr3 := rfl
  have hΛd : d.leaves ≤ W :=
    ((Batch1171.leaves_tail_le c _).trans (Batch1171.leaves_tail_le a _)).trans (I.win C).2
  obtain ⟨hslot, he⟩ := recW C I 2 h2 hrec2 (by show enc z d = u.label.1.2.2.1.mr3.root; rw [hmr3]; exact Batch1171.enc_eq_of_bind hd)
    hΛd I.bf.2.2
  cases d with
  | atom k => simp [Noun.slot] at hslot
  | cell e g =>
  change enc z (nounHead (Noun.cell e g)) = u.label.1.2.2.1.mr3.child at he
  rw [hmr3] at he
  simp only [nounHead] at he
  have heb : bindFP z e u.label.1.2.2.2.f_tth := he.symm
  refine ⟨e, g, rfl, heb, ?_⟩
  have hcc : FP.cons z u.label.1.2.2.2.f_tth (enc z g) =
      FP.cons z u.label.1.2.2.2.f_tth u.label.1.2.2.2.f_ttt := by
    have := Batch1171.enc_eq_of_bind hd
    rw [enc_cons C.hz, ← heb] at this
    rw [hcons]
    exact this
  have hne : u.label.1.2.2.2.f_tth.size ≠ 0 := by rw [heb]; exact Batch1171.enc_size_ne_zero C.hz e
  exact (Batch758.cons_right_cancel hne hcc).symm

theorem link_atW (C : CtxW (sv := sv) (ax := ax) z q W D t S0 F0)
    {row : (State × DTcomp K) × ℕ} {ch : List (NTree ((State × DTcomp K) × ℕ))}
    (hu : InTree t (.node row ch)) (k : Fin 3)
    {c : NTree ((State × DTcomp K) × ℕ)} (hc : ch[(k : ℕ)]? = some c) :
    c.label.1.2.2.1.s = (sfTriple row.1.2.2.1 k).1 ∧
      c.label.1.2.2.1.f = (sfTriple row.1.2.2.1 k).2.1 ∧
      c.label.1.2.2.1.e = (sfTriple row.1.2.2.1 k).2.2 := by
  have h := (C.row _ hu).link k c hc
  exact ⟨congrArg Prod.fst h, congrArg (fun p => p.2.1) h, congrArg (fun p => p.2.2) h⟩

end Shapes

set_option hygiene false in
/-- The FIELD C2 join at the field's own characteristic. -/
local notation "JR" => c2JoinFuelF (ringChar K) (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) sv ax

/-! ## §C  The step lemmas -/

section Steps

variable {z : K} {W D : ℕ} {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}

/-- **OP0** (no run: the tail is an atom by `f_t.size = z` and `LowOrderFree`). -/
theorem step_s0W (C : CtxW (sv := sv) (ax := ax) z (ringChar K) W D t S0 F0)
    {row : (State × DTcomp K) × ℕ} {s f : Noun}
    (I : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 (.node row []) s f) (hst : row.1.1 = .s0) :
    GoodW (sv := sv) (ax := ax) z (ringChar K) (.node row []) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0W C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row []).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atomW C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hmb : memBlk row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.1
  have hpubSt : row.1.2.2.1.state = .s0 := R.pubSt.trans hst
  simp only [memBlk, hpubSt] at hmb
  have hbL : b.leaves ≤ W := (Batch1171.leaves_tail_le _ b).trans (I.win C).2
  have hsz : (enc z b).size = z := by
    rw [Batch1171.enc_eq_of_bind hb]; exact hmb.2.2.2.1.trans R.zRow
  obtain ⟨ax', rfl⟩ := atom_of_size_z C.hz C.hW1 C.hlow hbL hsz
  have hax := R.ax0 hst
  have hleaf : row.1.2.2.2.f_t.leaf = (ax' : K) := Batch1171.atomFP_leaf_eq hb
  have haxeq : ax (row.2 + 2) = ax' := hax.1 ax' (by simpa using I.bf.2) hleaf
  have hcastK : ((ax (row.2 + 2) : ℕ) : K) = row.1.2.2.2.f_t.leaf := by rw [haxeq, hleaf]
  have hrec := C.recs _ s _ I.pr
  have h1 : (1 : ℕ) < Nock.Framework.recordCount (NTree.node row []).label.1.1 := by
    simp [hst, Nock.Framework.recordCount]
  have hj : ((1 : Fin 3) : ℕ) < Nock.Framework.recordCount
      (JR (NTree.node row []).size (.node row []) s (.cell (.atom 0) (.atom ax'))).label.state := by
    rw [J_label_eq]; exact h1
  have h := hrec 1 hj
  rw [J_rec] at h
  simp only [NTree.label, Fin.val_one] at h
  rw [hst, c2RecF_s0_1] at h
  have hmr : Batch1171.traceRec row 1 = row.1.2.2.1.mr2 := rfl
  rw [hmr, hmb.1] at h
  obtain ⟨hslot, he⟩ := h (Batch1171.enc_eq_of_bind I.hs) (I.win C).1 I.bs
  refine ⟨C2ChipReady.op0 hst R.zRow hpubSt ha hb he.symm hcastK R.vcomp,
    C2Aligned.op0 (a := ax') hst ?_⟩
  rw [← haxeq]; exact hslot

/-- **OP1.** -/
theorem step_s1W (C : CtxW (sv := sv) (ax := ax) z (ringChar K) W D t S0 F0)
    {row : (State × DTcomp K) × ℕ} {s f : Noun}
    (I : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 (.node row []) s f) (hst : row.1.1 = .s1) :
    GoodW (sv := sv) (ax := ax) z (ringChar K) (.node row []) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0W C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row []).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atomW C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s1 := R.pubSt.trans hst
  exact ⟨C2ChipReady.op1 hst R.zRow hpubSt ha hb R.vcomp, C2Aligned.op1 hst⟩

/-- **OP3** (the kid's size window from the call-tree premise). -/
theorem step_s3W (C : CtxW (sv := sv) (ax := ax) z (ringChar K) W D t S0 F0)
    {row : (State × DTcomp K) × ℕ} {c0 : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 (.node row [c0]) s f) (hst : row.1.1 = .s3)
    (IH : ∀ s' f', InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c0 s' f' →
      GoodW (sv := sv) (ax := ax) z (ringChar K) c0 s' f') :
    GoodW (sv := sv) (ax := ax) z (ringChar K) (.node row [c0]) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0W C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row [c0]).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atomW C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s3 := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  obtain ⟨m, hsz, hm⟩ := Batch1171.size_succ row [c0]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hch : (JR (NTree.node row [c0]).size (.node row [c0]) s (.cell (.atom 3) b)).children =
      [JR c0.size c0 s b] := by
    rw [hsz, J_s3 (q := (ringChar K)) (sv := sv) (ax := ax) _ _ row c0 hst]
    simp only [NTree.children, nounTail]
    rw [J_at_size (q := (ringChar K)) c0 s b hm0]
  obtain ⟨hls, hlf, hle⟩ := link_atW C I.inT 0 (c := c0) rfl
  simp only [sfTriple] at hls hlf hle
  have hs0 : bindFP z s c0.label.1.2.2.1.s := by rw [hls, hev.1]; exact I.hs
  have hf0 : bindFP z b c0.label.1.2.2.1.f := by rw [hlf, hev.2.1]; exact hb
  have I0 : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c0 s b :=
    ⟨Batch1171.inT_child I.inT (by simp), Batch1171.reach_child I.reach (by rw [hch]; simp),
      Batch1171.pr_child I.pr 0 (by simp) (by rw [hch]; simp),
      I.childCall (by omega) (fun _ h => .op3 h), I.bs, I.bf.2, hs0, hf0⟩
  have G0 := IH s b I0
  have hwinN := sizeWindow_of_lowOrderFree C.hz C.hW1 C.hlow (kidWin C I0 G0)
  exact ⟨C2ChipReady.op3 hst R.zRow hpubSt ha hb R.vcomp hwinN hle hls G0.1,
    C2Aligned.op3 hst G0.2⟩

/-- **OP4** (the kid's result is an atom by `sf1_e.size = z` and the call-tree window). -/
theorem step_s4W (C : CtxW (sv := sv) (ax := ax) z (ringChar K) W D t S0 F0)
    {row : (State × DTcomp K) × ℕ} {c0 : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 (.node row [c0]) s f) (hst : row.1.1 = .s4)
    (IH : ∀ s' f', InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c0 s' f' →
      GoodW (sv := sv) (ax := ax) z (ringChar K) c0 s' f') :
    GoodW (sv := sv) (ax := ax) z (ringChar K) (.node row [c0]) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0W C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row [c0]).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atomW C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s4 := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  obtain ⟨m, hsz, hm⟩ := Batch1171.size_succ row [c0]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hch : (JR (NTree.node row [c0]).size (.node row [c0]) s (.cell (.atom 4) b)).children =
      [JR c0.size c0 s b] := by
    rw [hsz, J_s4 (q := (ringChar K)) (sv := sv) (ax := ax) _ _ row c0 hst]
    simp only [NTree.children, nounTail]
    rw [J_at_size (q := (ringChar K)) c0 s b hm0]
  obtain ⟨hls, hlf, hle⟩ := link_atW C I.inT 0 (c := c0) rfl
  simp only [sfTriple] at hls hlf hle
  have hs0 : bindFP z s c0.label.1.2.2.1.s := by rw [hls, hev.1]; exact I.hs
  have hf0 : bindFP z b c0.label.1.2.2.1.f := by rw [hlf, hev.2.1]; exact hb
  have I0 : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c0 s b :=
    ⟨Batch1171.inT_child I.inT (by simp), Batch1171.reach_child I.reach (by rw [hch]; simp),
      Batch1171.pr_child I.pr 0 (by simp) (by rw [hch]; simp),
      I.childCall (by omega) (fun _ h => .op4 h), I.bs, I.bf.2, hs0, hf0⟩
  have G0 := IH s b I0
  have he0b := kid_e_bind (q := (ringChar K)) C.hz G0.1 hs0
  have hsize : (enc z (JR c0.size c0 s b).label.evaluation).size = z := by
    rw [Batch1171.enc_eq_of_bind he0b, hle, hev.2.2.1]; exact R.zRow
  obtain ⟨k, hke⟩ := atom_of_size_z C.hz C.hW1 C.hlow (kidWin C I0 G0) hsize
  exact ⟨C2ChipReady.op4 hst R.zRow hpubSt ha hb R.vcomp hke hle hls G0.1,
    C2Aligned.op4 hst G0.2⟩

/-- **cons.** -/
theorem step_consW (C : CtxW (sv := sv) (ax := ax) z (ringChar K) W D t S0 F0)
    {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 (.node row [c0, c1]) s f) (hst : row.1.1 = .cons)
    (IH0 : ∀ s' f', InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c0 s' f' →
      GoodW (sv := sv) (ax := ax) z (ringChar K) c0 s' f')
    (IH1 : ∀ s' f', InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c1 s' f' →
      GoodW (sv := sv) (ax := ax) z (ringChar K) c1 s' f') :
    GoodW (sv := sv) (ax := ax) z (ringChar K) (.node row [c0, c1]) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0W C I
  have R := C.row _ I.inT
  obtain ⟨lh, lt, rfl⟩ := head_cellW C I hst ha
  have hpubSt : row.1.2.2.1.state = .cons := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  obtain ⟨m, hsz, hm⟩ := Batch1171.size_succ row [c0, c1]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hm1 : c1.size ≤ m := hm c1 (by simp)
  have hch : (JR (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
      (.cell (.cell lh lt) b)).children = [JR c0.size c0 s (.cell lh lt), JR c1.size c1 s b] := by
    rw [hsz, J_cons (q := (ringChar K)) (sv := sv) (ax := ax) _ _ row c0 c1 hst]
    simp only [NTree.children, nounHead, nounTail]
    rw [J_at_size (q := (ringChar K)) c0 _ _ hm0, J_at_size (q := (ringChar K)) c1 _ _ hm1]
  obtain ⟨hls0, hlf0, hle0⟩ := link_atW C I.inT 0 (c := c0) rfl
  obtain ⟨hls1, hlf1, hle1⟩ := link_atW C I.inT 1 (c := c1) rfl
  simp only [sfTriple] at hls0 hlf0 hle0 hls1 hlf1 hle1
  have hs0 : bindFP z s c0.label.1.2.2.1.s := by rw [hls0, hev.1]; exact I.hs
  have hf0 : bindFP z (.cell lh lt) c0.label.1.2.2.1.f := by rw [hlf0, hev.2.1]; exact ha
  have hs1 : bindFP z s c1.label.1.2.2.1.s := by rw [hls1, hev.2.2.1]; exact I.hs
  have hf1 : bindFP z b c1.label.1.2.2.1.f := by rw [hlf1, hev.2.2.2.1]; exact hb
  have I0 : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c0 s (.cell lh lt) :=
    ⟨Batch1171.inT_child I.inT (by simp), Batch1171.reach_child I.reach (by rw [hch]; simp),
      Batch1171.pr_child I.pr 0 (by simp) (by rw [hch]; simp),
      I.childCall (by omega) (fun _ h => .consL h), I.bs, I.bf.1, hs0, hf0⟩
  have G0 := IH0 _ _ I0
  have I1 : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c1 s b :=
    ⟨Batch1171.inT_child I.inT (by simp), Batch1171.reach_child I.reach (by rw [hch]; simp),
      Batch1171.pr_child I.pr 1 (by simp) (by rw [hch]; simp),
      I.childCall (by omega) (fun _ h => .consR h), I.bs, I.bf.2, hs1, hf1⟩
  have G1 := IH1 _ _ I1
  exact ⟨C2ChipReady.cons hst R.zRow hpubSt ha hb R.vcomp hle0 hle1 hls0 hls1 G0.1 G1.1,
    C2Aligned.cons hst G0.2 G1.2⟩

/-- **OP5** (`PairFaithful` from the census at the kids' windowed, bounded evaluations). -/
theorem step_s5W (C : CtxW (sv := sv) (ax := ax) z (ringChar K) W D t S0 F0)
    {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 (.node row [c0, c1]) s f) (hst : row.1.1 = .s5)
    (IH0 : ∀ s' f', InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c0 s' f' →
      GoodW (sv := sv) (ax := ax) z (ringChar K) c0 s' f')
    (IH1 : ∀ s' f', InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c1 s' f' →
      GoodW (sv := sv) (ax := ax) z (ringChar K) c1 s' f') :
    GoodW (sv := sv) (ax := ax) z (ringChar K) (.node row [c0, c1]) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0W C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row [c0, c1]).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atomW C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s5 := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  have hmb : memBlk row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.1
  simp only [memBlk, hpubSt] at hmb
  have hzr : row.1.2.1.z = z := R.zRow
  have hcons2 := hmb.2.1
  rw [hzr] at hcons2
  obtain ⟨c, d, rfl, hc, hd⟩ := tail_bind2W C I hb
    (by simp [NTree.label, hst, Nock.Framework.recordCount])
    (by simp only [NTree.label]; rw [hst, c2RecF_s5_1]; rfl) ⟨_, hmb.1⟩ hcons2
  obtain ⟨m, hsz, hm⟩ := Batch1171.size_succ row [c0, c1]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hm1 : c1.size ≤ m := hm c1 (by simp)
  have hch : (JR (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
      (.cell (.atom 5) (.cell c d))).children = [JR c0.size c0 s c, JR c1.size c1 s d] := by
    rw [hsz, J_s5 (q := (ringChar K)) (sv := sv) (ax := ax) _ _ row c0 c1 hst]
    simp only [NTree.children, nounHead, nounTail]
    rw [J_at_size (q := (ringChar K)) c0 _ _ hm0, J_at_size (q := (ringChar K)) c1 _ _ hm1]
  obtain ⟨hls0, hlf0, hle0⟩ := link_atW C I.inT 0 (c := c0) rfl
  obtain ⟨hls1, hlf1, hle1⟩ := link_atW C I.inT 1 (c := c1) rfl
  simp only [sfTriple] at hls0 hlf0 hle0 hls1 hlf1 hle1
  have hs0 : bindFP z s c0.label.1.2.2.1.s := by rw [hls0, hev.1]; exact I.hs
  have hf0 : bindFP z c c0.label.1.2.2.1.f := by rw [hlf0, hev.2.1]; exact hc
  have hs1 : bindFP z s c1.label.1.2.2.1.s := by rw [hls1, hev.2.2.1]; exact I.hs
  have hf1 : bindFP z d c1.label.1.2.2.1.f := by rw [hlf1, hev.2.2.2.1]; exact hd
  have I0 : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c0 s c :=
    ⟨Batch1171.inT_child I.inT (by simp), Batch1171.reach_child I.reach (by rw [hch]; simp),
      Batch1171.pr_child I.pr 0 (by simp) (by rw [hch]; simp),
      I.childCall (by omega) (fun _ h => .op5L h), I.bs, I.bf.2.1, hs0, hf0⟩
  have G0 := IH0 _ _ I0
  have I1 : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c1 s d :=
    ⟨Batch1171.inT_child I.inT (by simp), Batch1171.reach_child I.reach (by rw [hch]; simp),
      Batch1171.pr_child I.pr 1 (by simp) (by rw [hch]; simp),
      I.childCall (by omega) (fun _ h => .op5R h), I.bs, I.bf.2.2, hs1, hf1⟩
  have G1 := IH1 _ _ I1
  have hfaith : OpcodeSemantics.PairFaithful z (ringChar K) (JR c0.size c0 s c).label.evaluation
      (JR c1.size c1 s d).label.evaluation := by
    have hcen := C.census _ s _ I.inT I.reach
    refine ⟨hcen (P8Census.skeletonUse .equalityOperand (JR c0.size c0 s c).label.evaluation
        (JR c1.size c1 s d).label.evaluation) ?_ (kidWin C I0 G0) (kidWin C I1 G1),
      kidBounded C G0 I.bs I.bf.2.1, kidBounded C G1 I.bs I.bf.2.2⟩
    rw [J_label_eq]
    simp only [NTree.label, hst, hch]
    simp [P8Census.skeletonComparisons, c2SkeletonRowF, P8Census.skeletonSubformula, fanoutComp,
      P8Census.skeletonUse]
    exact ⟨rfl, rfl⟩
  exact ⟨C2ChipReady.op5 hst R.zRow hpubSt ha hc hd R.vcomp C.hcast hfaith hle0 hle1 hls0 hls1
      G0.1 G1.1,
    C2Aligned.op5 hst G0.2 G1.2⟩

/-- **OP2** (the applied kid's inputs are the field runs of the first two kids). -/
theorem step_s2W (C : CtxW (sv := sv) (ax := ax) z (ringChar K) W D t S0 F0)
    {row : (State × DTcomp K) × ℕ} {c0 c1 c2 : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 (.node row [c0, c1, c2]) s f) (hst : row.1.1 = .s2)
    (IH0 : ∀ s' f', InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c0 s' f' →
      GoodW (sv := sv) (ax := ax) z (ringChar K) c0 s' f')
    (IH1 : ∀ s' f', InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c1 s' f' →
      GoodW (sv := sv) (ax := ax) z (ringChar K) c1 s' f')
    (IH2 : ∀ s' f', InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c2 s' f' →
      GoodW (sv := sv) (ax := ax) z (ringChar K) c2 s' f') :
    GoodW (sv := sv) (ax := ax) z (ringChar K) (.node row [c0, c1, c2]) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0W C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row [c0, c1, c2]).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atomW C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s2 := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  have hmb : memBlk row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.1
  simp only [memBlk, hpubSt] at hmb
  have hzr : row.1.2.1.z = z := R.zRow
  have hcons2 := hmb.2.1
  rw [hzr] at hcons2
  obtain ⟨c, d, rfl, hc, hd⟩ := tail_bind2W C I hb
    (by simp [NTree.label, hst, Nock.Framework.recordCount])
    (by simp only [NTree.label]; rw [hst, c2RecF_s2_1]; rfl) ⟨_, hmb.1⟩ hcons2
  obtain ⟨m, hsz, hm⟩ := Batch1171.size_succ row [c0, c1, c2]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hm1 : c1.size ≤ m := hm c1 (by simp)
  have hm2 : c2.size ≤ m := hm c2 (by simp)
  have hch : (JR (NTree.node row [c0, c1, c2]).size (.node row [c0, c1, c2]) s
      (.cell (.atom 2) (.cell c d))).children =
      [JR c0.size c0 s c, JR c1.size c1 s d,
        JR c2.size c2 (JR c0.size c0 s c).label.evaluation (JR c1.size c1 s d).label.evaluation] := by
    rw [hsz, J_s2 (q := (ringChar K)) (sv := sv) (ax := ax) _ _ row c0 c1 c2 hst]
    simp only [NTree.children, nounHead, nounTail]
    rw [J_at_size (q := (ringChar K)) c0 _ _ hm0, J_at_size (q := (ringChar K)) c1 _ _ hm1, J_at_size (q := (ringChar K)) c2 _ _ hm2]
  obtain ⟨hls0, hlf0, hle0⟩ := link_atW C I.inT 0 (c := c0) rfl
  obtain ⟨hls1, hlf1, hle1⟩ := link_atW C I.inT 1 (c := c1) rfl
  obtain ⟨hls2, hlf2, hle2⟩ := link_atW C I.inT 2 (c := c2) rfl
  simp only [sfTriple] at hls0 hlf0 hle0 hls1 hlf1 hle1 hls2 hlf2 hle2
  have hs0 : bindFP z s c0.label.1.2.2.1.s := by rw [hls0, hev.1]; exact I.hs
  have hf0 : bindFP z c c0.label.1.2.2.1.f := by rw [hlf0, hev.2.1]; exact hc
  have hs1 : bindFP z s c1.label.1.2.2.1.s := by rw [hls1, hev.2.2.1]; exact I.hs
  have hf1 : bindFP z d c1.label.1.2.2.1.f := by rw [hlf1, hev.2.2.2.1]; exact hd
  have I0 : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c0 s c :=
    ⟨Batch1171.inT_child I.inT (by simp), Batch1171.reach_child I.reach (by rw [hch]; simp),
      Batch1171.pr_child I.pr 0 (by simp) (by rw [hch]; simp),
      I.childCall (by omega) (fun _ h => .op2L h), I.bs, I.bf.2.1, hs0, hf0⟩
  have G0 := IH0 _ _ I0
  have I1 : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c1 s d :=
    ⟨Batch1171.inT_child I.inT (by simp), Batch1171.reach_child I.reach (by rw [hch]; simp),
      Batch1171.pr_child I.pr 1 (by simp) (by rw [hch]; simp),
      I.childCall (by omega) (fun _ h => .op2R h), I.bs, I.bf.2.2, hs1, hf1⟩
  have G1 := IH1 _ _ I1
  obtain ⟨n0, r0⟩ := kidRun G0
  obtain ⟨n1, r1⟩ := kidRun G1
  have he0b := kid_e_bind (q := (ringChar K)) C.hz G0.1 hs0
  have he1b := kid_e_bind (q := (ringChar K)) C.hz G1.1 hs1
  have hs2 : bindFP z (JR c0.size c0 s c).label.evaluation c2.label.1.2.2.1.s := by
    rw [hls2, hev.2.2.2.2.1, ← hle0]; exact he0b
  have hf2 : bindFP z (JR c1.size c1 s d).label.evaluation c2.label.1.2.2.1.f := by
    rw [hlf2, hev.2.2.2.2.2.1, ← hle1]; exact he1b
  have I2 : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c2 (JR c0.size c0 s c).label.evaluation
      (JR c1.size c1 s d).label.evaluation :=
    ⟨Batch1171.inT_child I.inT (by simp), Batch1171.reach_child I.reach (by rw [hch]; simp),
      Batch1171.pr_child I.pr 2 (by simp) (by rw [hch]; simp),
      I.childCall (by omega) (fun _ h => .op2App h r0 r1),
      kidBounded C G0 I.bs I.bf.2.1, kidBounded C G1 I.bs I.bf.2.2, hs2, hf2⟩
  have G2 := IH2 _ _ I2
  exact ⟨C2ChipReady.op2 hst R.zRow hpubSt ha hc hd R.vcomp hle0 hle1 hle2 hls0 hls1 hls2
      G0.1 G1.1 G2.1,
    C2Aligned.op2 hst G0.2 G1.2 G2.2⟩

/-- **OP7** (the mutated subject is the helper kid's field run). -/
theorem step_s7W (C : CtxW (sv := sv) (ax := ax) z (ringChar K) W D t S0 F0)
    {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 (.node row [c0, c1]) s f) (hst : row.1.1 = .s7)
    (IH0 : ∀ s' f', InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c0 s' f' →
      GoodW (sv := sv) (ax := ax) z (ringChar K) c0 s' f')
    (IH1 : ∀ s' f', InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c1 s' f' →
      GoodW (sv := sv) (ax := ax) z (ringChar K) c1 s' f') :
    GoodW (sv := sv) (ax := ax) z (ringChar K) (.node row [c0, c1]) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0W C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row [c0, c1]).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atomW C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s7 := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  have hmb : memBlk row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.1
  simp only [memBlk, hpubSt] at hmb
  have hzr : row.1.2.1.z = z := R.zRow
  have hcons2 := hmb.2.1
  rw [hzr] at hcons2
  obtain ⟨c, d, rfl, hc, hd⟩ := tail_bind2W C I hb
    (by simp [NTree.label, hst, Nock.Framework.recordCount])
    (by simp only [NTree.label]; rw [hst, c2RecF_s7_1]; rfl) ⟨_, hmb.1⟩ hcons2
  obtain ⟨m, hsz, hm⟩ := Batch1171.size_succ row [c0, c1]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hm1 : c1.size ≤ m := hm c1 (by simp)
  have hch : (JR (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
      (.cell (.atom 7) (.cell c d))).children =
      [JR c0.size c0 (JR c1.size c1 s c).label.evaluation d, JR c1.size c1 s c] := by
    rw [hsz, J_s7 (q := (ringChar K)) (sv := sv) (ax := ax) _ _ row c0 c1 hst]
    simp only [NTree.children, nounHead, nounTail]
    rw [J_at_size (q := (ringChar K)) c1 _ _ hm1, J_at_size (q := (ringChar K)) c0 _ _ hm0]
  obtain ⟨hls0, hlf0, hle0⟩ := link_atW C I.inT 0 (c := c0) rfl
  obtain ⟨hls1, hlf1, hle1⟩ := link_atW C I.inT 1 (c := c1) rfl
  simp only [sfTriple] at hls0 hlf0 hle0 hls1 hlf1 hle1
  have hs1 : bindFP z s c1.label.1.2.2.1.s := by rw [hls1, hev.2.2.2.1]; exact I.hs
  have hf1 : bindFP z c c1.label.1.2.2.1.f := by rw [hlf1, hev.2.2.2.2.1]; exact hc
  have I1 : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c1 s c :=
    ⟨Batch1171.inT_child I.inT (by simp), Batch1171.reach_child I.reach (by rw [hch]; simp),
      Batch1171.pr_child I.pr 1 (by simp) (by rw [hch]; simp),
      I.childCall (by omega) (fun _ h => .op7H h), I.bs, I.bf.2.1, hs1, hf1⟩
  have G1 := IH1 _ _ I1
  obtain ⟨n1, r1⟩ := kidRun G1
  have he1b := kid_e_bind (q := (ringChar K)) C.hz G1.1 hs1
  have hs0 : bindFP z (JR c1.size c1 s c).label.evaluation c0.label.1.2.2.1.s := by
    rw [hls0, hev.1, ← hle1]; exact he1b
  have hf0 : bindFP z d c0.label.1.2.2.1.f := by rw [hlf0, hev.2.1]; exact hd
  have I0 : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c0 (JR c1.size c1 s c).label.evaluation d :=
    ⟨Batch1171.inT_child I.inT (by simp), Batch1171.reach_child I.reach (by rw [hch]; simp),
      Batch1171.pr_child I.pr 0 (by simp) (by rw [hch]; simp),
      I.childCall (by omega) (fun _ h => .op7M h r1),
      kidBounded C G1 I.bs I.bf.2.1, I.bf.2.2, hs0, hf0⟩
  have G0 := IH0 _ _ I0
  exact ⟨C2ChipReady.op7 hst R.zRow hpubSt ha hc hd R.vcomp hle1 hle0 hls1 hls0 G1.1 G0.1,
    C2Aligned.op7 hst G1.2 G0.2⟩

/-- **OP8** (the pushed subject is the helper kid's field run consed on the subject). -/
theorem step_s8W (C : CtxW (sv := sv) (ax := ax) z (ringChar K) W D t S0 F0)
    {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 (.node row [c0, c1]) s f) (hst : row.1.1 = .s8)
    (IH0 : ∀ s' f', InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c0 s' f' →
      GoodW (sv := sv) (ax := ax) z (ringChar K) c0 s' f')
    (IH1 : ∀ s' f', InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c1 s' f' →
      GoodW (sv := sv) (ax := ax) z (ringChar K) c1 s' f') :
    GoodW (sv := sv) (ax := ax) z (ringChar K) (.node row [c0, c1]) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0W C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row [c0, c1]).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atomW C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s8 := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  have hmb : memBlk row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.1
  simp only [memBlk, hpubSt] at hmb
  have hzr : row.1.2.1.z = z := R.zRow
  have hcons2 := hmb.2.1
  rw [hzr] at hcons2
  obtain ⟨c, d, rfl, hc, hd⟩ := tail_bind2W C I hb
    (by simp [NTree.label, hst, Nock.Framework.recordCount])
    (by simp only [NTree.label]; rw [hst, c2RecF_s8_1]; rfl) ⟨_, hmb.1⟩ hcons2
  obtain ⟨m, hsz, hm⟩ := Batch1171.size_succ row [c0, c1]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hm1 : c1.size ≤ m := hm c1 (by simp)
  have hch : (JR (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
      (.cell (.atom 8) (.cell c d))).children =
      [JR c0.size c0 (.cell (JR c1.size c1 s c).label.evaluation s) d, JR c1.size c1 s c] := by
    rw [hsz, J_s8 (q := (ringChar K)) (sv := sv) (ax := ax) _ _ row c0 c1 hst]
    simp only [NTree.children, nounHead, nounTail]
    rw [J_at_size (q := (ringChar K)) c1 _ _ hm1, J_at_size (q := (ringChar K)) c0 _ _ hm0]
  obtain ⟨hls0, hlf0, hle0⟩ := link_atW C I.inT 0 (c := c0) rfl
  obtain ⟨hls1, hlf1, hle1⟩ := link_atW C I.inT 1 (c := c1) rfl
  simp only [sfTriple] at hls0 hlf0 hle0 hls1 hlf1 hle1
  have hs1 : bindFP z s c1.label.1.2.2.1.s := by rw [hls1, hev.2.2.2.1]; exact I.hs
  have hf1 : bindFP z c c1.label.1.2.2.1.f := by rw [hlf1, hev.2.2.2.2.1]; exact hc
  have I1 : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c1 s c :=
    ⟨Batch1171.inT_child I.inT (by simp), Batch1171.reach_child I.reach (by rw [hch]; simp),
      Batch1171.pr_child I.pr 1 (by simp) (by rw [hch]; simp),
      I.childCall (by omega) (fun _ h => .op8H h), I.bs, I.bf.2.1, hs1, hf1⟩
  have G1 := IH1 _ _ I1
  obtain ⟨n1, r1⟩ := kidRun G1
  have he1b := kid_e_bind (q := (ringChar K)) C.hz G1.1 hs1
  have hs0 : bindFP z (.cell (JR c1.size c1 s c).label.evaluation s) c0.label.1.2.2.1.s := by
    rw [hls0, hev.1, hzr]
    exact Batch525.bindFP_cons C.hz _ _ _ _ (hle1 ▸ he1b) I.hs
  have hf0 : bindFP z d c0.label.1.2.2.1.f := by rw [hlf0, hev.2.1]; exact hd
  have I0 : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c0
      (.cell (JR c1.size c1 s c).label.evaluation s) d :=
    ⟨Batch1171.inT_child I.inT (by simp), Batch1171.reach_child I.reach (by rw [hch]; simp),
      Batch1171.pr_child I.pr 0 (by simp) (by rw [hch]; simp),
      I.childCall (by omega) (fun _ h => .op8M h r1),
      ⟨kidBounded C G1 I.bs I.bf.2.1, I.bs⟩, I.bf.2.2, hs0, hf0⟩
  have G0 := IH0 _ _ I0
  exact ⟨C2ChipReady.op8 hst R.zRow hpubSt ha hc hd R.vcomp hle1 hle0 hls1 hls0 G1.1 G0.1,
    C2Aligned.op8 hst G1.2 G0.2⟩

/-- **OP6** (the selector is an atom `0`/`1` by the chip's own gates, `LowOrderFree` and `hcast`). -/
theorem step_s6W (C : CtxW (sv := sv) (ax := ax) z (ringChar K) W D t S0 F0)
    {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 (.node row [c0, c1]) s f) (hst : row.1.1 = .s6)
    (IH0 : ∀ s' f', InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c0 s' f' →
      GoodW (sv := sv) (ax := ax) z (ringChar K) c0 s' f')
    (IH1 : ∀ s' f', InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c1 s' f' →
      GoodW (sv := sv) (ax := ax) z (ringChar K) c1 s' f') :
    GoodW (sv := sv) (ax := ax) z (ringChar K) (.node row [c0, c1]) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0W C I
  have R := C.row _ I.inT
  have hz' : row.1.2.1.z = z := R.zRow
  have hcons : (NTree.node row [c0, c1]).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atomW C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s6 := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  have hmb : memBlk row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.1
  simp only [memBlk, hpubSt] at hmb
  have hcons1 : FP.cons z row.1.2.2.2.f_th row.1.2.2.2.f_tt = row.1.2.2.2.f_t := by
    rw [← hz']; exact hmb.2.1
  have hcons2 : FP.cons z row.1.2.2.2.f_tth row.1.2.2.2.f_ttt = row.1.2.2.2.f_tt := by
    rw [← hz']; exact hmb.2.2.2.1
  obtain ⟨c, b2, rfl, hc, hde⟩ := tail_bind2W C I hb
    (by simp [NTree.label, hst, Nock.Framework.recordCount])
    (by simp only [NTree.label]; rw [hst, c2RecF_s6_1]; rfl) ⟨_, hmb.1⟩ hcons1
  obtain ⟨d, e, rfl, hd, he⟩ := tail_bind3W C I hde
    (by simp [NTree.label, hst, Nock.Framework.recordCount])
    (by simp only [NTree.label]; rw [hst, c2RecF_s6_2]; rfl) ⟨_, hmb.2.2.1⟩ hcons2
  obtain ⟨m, hsz, hm⟩ := Batch1171.size_succ row [c0, c1]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hm1 : c1.size ≤ m := hm c1 (by simp)
  have hch : (JR (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
      (.cell (.atom 6) (.cell c (.cell d e)))).children =
      [JR c0.size c0 s (if Batch1091.c6b (JR c1.size c1 s c).label.evaluation = 0 then d else e),
        JR c1.size c1 s c] := by
    rw [hsz, J_s6 (q := (ringChar K)) (sv := sv) (ax := ax) _ _ row c0 c1 hst]
    simp only [NTree.children, nounHead, nounTail]
    simp only [J_at_size (q := (ringChar K)) c1 _ _ hm1, J_at_size (q := (ringChar K)) c0 _ _ hm0]
    rfl
  obtain ⟨hls0, hlf0, hle0⟩ := link_atW C I.inT 0 (c := c0) rfl
  obtain ⟨hls1, hlf1, hle1⟩ := link_atW C I.inT 1 (c := c1) rfl
  simp only [sfTriple] at hls0 hlf0 hle0 hls1 hlf1 hle1
  have hs1 : bindFP z s c1.label.1.2.2.1.s := by rw [hls1, hev.2.2.2.1]; exact I.hs
  have hf1 : bindFP z c c1.label.1.2.2.1.f := by rw [hlf1, hev.2.2.2.2.1]; exact hc
  have I1 : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c1 s c :=
    ⟨Batch1171.inT_child I.inT (by simp), Batch1171.reach_child I.reach (by rw [hch]; simp),
      Batch1171.pr_child I.pr 1 (by simp) (by rw [hch]; simp),
      I.childCall (by omega) (fun _ h => .op6C h), I.bs, I.bf.2.1, hs1, hf1⟩
  have G1 := IH1 _ _ I1
  obtain ⟨n1, r1⟩ := kidRun G1
  have he1b := kid_e_bind (q := (ringChar K)) C.hz G1.1 hs1
  -- the selector is an atom (`sf2_e.size = z`, window) with leaf `0` or `1`, below `(ringChar K)`
  have hsize : (enc z (JR c1.size c1 s c).label.evaluation).size = z := by
    rw [Batch1171.enc_eq_of_bind he1b, hle1, hev.2.2.2.2.2.1]; exact hz'
  obtain ⟨bb, hev1⟩ := atom_of_size_z C.hz C.hW1 C.hlow (kidWin C I1 G1) hsize
  have hbq : bb < (ringChar K) := by
    have := kidBounded C G1 I.bs I.bf.2.1
    rw [hev1] at this; simpa using this
  have he1b' := he1b
  rw [hev1] at he1b'
  have hleaf : row.1.2.2.1.sf2_e.leaf = (bb : K) := by
    rw [← hle1]; exact Batch1171.atomFP_leaf_eq he1b'
  have hb01 : bb = 0 ∨ bb = 1 := by
    have hq := C.hq12
    rcases hev.2.2.2.2.2.2.2.1 with h0 | h1
    · left
      rw [hleaf] at h0
      exact C.hcast (Set.mem_Iio.mpr hbq) (Set.mem_Iio.mpr (by omega)) (by simpa using h0)
    · right
      rw [hleaf] at h1
      exact C.hcast (Set.mem_Iio.mpr hbq) (Set.mem_Iio.mpr (by omega)) (by simpa using h1)
  have hb' : Batch1091.c6b (JR c1.size c1 s c).label.evaluation = bb := by rw [hev1]; rfl
  rw [hb'] at hch
  have hf0 : bindFP z (if bb = 0 then d else e) c0.label.1.2.2.1.f := by
    rw [hlf0, hev.2.1, hleaf]
    rcases hb01 with rfl | rfl
    · simpa using hd
    · simpa using he
  have hs0 : bindFP z s c0.label.1.2.2.1.s := by rw [hls0, hev.1]; exact I.hs
  have bf0 : BoundedBy (ringChar K) (if bb = 0 then d else e) := by
    rcases hb01 with rfl | rfl
    · simpa using I.bf.2.2.1
    · simpa using I.bf.2.2.2
  have hstepT : ∀ dd, CallTreeF (ringChar K) S0 F0 dd s (.cell (.atom 6) (.cell c (.cell d e))) →
      CallTreeF (ringChar K) S0 F0 (dd + 1) s (if bb = 0 then d else e) := by
    intro dd h
    have := CallTreeF.op6T h r1
    rw [hev1] at this
    exact this
  have I0 : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c0 s (if bb = 0 then d else e) :=
    ⟨Batch1171.inT_child I.inT (by simp), Batch1171.reach_child I.reach (by rw [hch]; simp),
      Batch1171.pr_child I.pr 0 (by simp) (by rw [hch]; simp),
      I.childCall (by omega) hstepT, I.bs, bf0, hs0, hf0⟩
  have G0 := IH0 _ _ I0
  refine ⟨C2ChipReady.op6 hst R.zRow hpubSt ha hc hd he hb01 hev1 R.vcomp hle0 hle1 hls0 hls1
      G0.1 G1.1, C2Aligned.op6 hst G1.2 ?_⟩
  rw [hb']; exact G0.2

/-- **OP9** (the axis operand is an atom by `f_th.size = z`; the arm is served at the core's slot). -/
theorem step_s9W (C : CtxW (sv := sv) (ax := ax) z (ringChar K) W D t S0 F0)
    {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 (.node row [c0, c1]) s f) (hst : row.1.1 = .s9)
    (IH0 : ∀ s' f', InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c0 s' f' →
      GoodW (sv := sv) (ax := ax) z (ringChar K) c0 s' f')
    (IH1 : ∀ s' f', InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c1 s' f' →
      GoodW (sv := sv) (ax := ax) z (ringChar K) c1 s' f') :
    GoodW (sv := sv) (ax := ax) z (ringChar K) (.node row [c0, c1]) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0W C I
  have R := C.row _ I.inT
  have hz' : row.1.2.1.z = z := R.zRow
  have hcons : (NTree.node row [c0, c1]).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atomW C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s9 := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  have hmb : memBlk row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.1
  simp only [memBlk, hpubSt] at hmb
  have hcons1 : FP.cons z row.1.2.2.2.f_th row.1.2.2.2.f_tt = row.1.2.2.2.f_t := by
    rw [← hz']; exact hmb.2.1
  obtain ⟨b1, c, rfl, hth, hc⟩ := tail_bind2W C I hb
    (by simp [NTree.label, hst, Nock.Framework.recordCount])
    (by simp only [NTree.label]; rw [hst, c2RecF_s9_1]; rfl) ⟨_, hmb.1⟩ hcons1
  -- the axis operand is an atom: `f_th.size = z` + the window
  have hb1L : b1.leaves ≤ W :=
    ((Batch1171.leaves_head_le b1 c).trans (Batch1171.leaves_tail_le _ _)).trans (I.win C).2
  have hsz1 : (enc z b1).size = z := by
    rw [Batch1171.enc_eq_of_bind hth]; exact (Vcomp.s9_axis_atom_shape hpubSt R.vcomp).1.trans hz'
  obtain ⟨ax', rfl⟩ := atom_of_size_z C.hz C.hW1 C.hlow hb1L hsz1
  have hax := R.ax9 hst
  have hleaf : row.1.2.2.2.f_th.leaf = (ax' : K) := Batch1171.atomFP_leaf_eq hth
  have haxeq : ax (row.2 + 3) = ax' := hax.1 ax' (by simpa using I.bf.2.1) hleaf
  subst haxeq
  obtain ⟨m, hsz, hm⟩ := Batch1171.size_succ row [c0, c1]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hm1 : c1.size ≤ m := hm c1 (by simp)
  have hch : (JR (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
      (.cell (.atom 9) (.cell (.atom (ax (row.2 + 3))) c))).children =
      [JR c0.size c0 s c,
        JR c1.size c1 (JR c0.size c0 s c).label.evaluation (op9ArmF sv ax row.2 (JR c0.size c0 s c).label.evaluation)] := by
    rw [hsz, J_s9 (q := (ringChar K)) (sv := sv) (ax := ax) _ _ row c0 c1 hst]
    simp only [NTree.children, nounHead, nounTail]
    rw [J_at_size (q := (ringChar K)) c0 _ _ hm0, J_at_size (q := (ringChar K)) c1 _ _ hm1]
  obtain ⟨hls0, hlf0, hle0⟩ := link_atW C I.inT 0 (c := c0) rfl
  obtain ⟨hls1, hlf1, hle1⟩ := link_atW C I.inT 1 (c := c1) rfl
  simp only [sfTriple] at hls0 hlf0 hle0 hls1 hlf1 hle1
  have hs0 : bindFP z s c0.label.1.2.2.1.s := by rw [hls0, hev.1]; exact I.hs
  have hf0 : bindFP z c c0.label.1.2.2.1.f := by rw [hlf0, hev.2.1]; exact hc
  have I0 : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c0 s c :=
    ⟨Batch1171.inT_child I.inT (by simp), Batch1171.reach_child I.reach (by rw [hch]; simp),
      Batch1171.pr_child I.pr 0 (by simp) (by rw [hch]; simp),
      I.childCall (by omega) (fun _ h => .op9C h), I.bs, I.bf.2.2, hs0, hf0⟩
  have G0 := IH0 _ _ I0
  obtain ⟨n0, r0⟩ := kidRun G0
  have he0b := kid_e_bind (q := (ringChar K)) C.hz G0.1 hs0
  have hcoreB := kidBounded C G0 I.bs I.bf.2.2
  -- record 2: the served arm is the slot of the core
  have hrec := C.recs _ s _ I.pr
  have hj2 : ((2 : Fin 3) : ℕ) < Nock.Framework.recordCount
      (JR (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
        (.cell (.atom 9) (.cell (.atom (ax (row.2 + 3))) c))).label.state := by
    rw [J_label_eq]; simp [hst, Nock.Framework.recordCount]
  have h2 := hrec 2 hj2
  rw [J_rec] at h2
  simp only [NTree.label, Fin.val_two] at h2
  rw [hst, c2RecF_s9_2, hch] at h2
  simp only [kidSkel, List.map_cons, List.map_nil, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, J_formula'] at h2
  have hmr : Batch1171.traceRec row 2 = row.1.2.2.1.mr3 := rfl
  rw [hmr, hmb.2.2.1] at h2
  obtain ⟨hslot', harm⟩ := h2 (by rw [← hle0]; exact Batch1171.enc_eq_of_bind he0b)
    (kidWin C I0 G0) hcoreB
  have hs1 : bindFP z (JR c0.size c0 s c).label.evaluation c1.label.1.2.2.1.s := by
    rw [hls1, hev.2.2.1, ← hle0]; exact he0b
  have hf1 : bindFP z (op9ArmF sv ax row.2 (JR c0.size c0 s c).label.evaluation) c1.label.1.2.2.1.f := by
    rw [hlf1]; exact harm.symm
  have I1 : InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c1 (JR c0.size c0 s c).label.evaluation
      (op9ArmF sv ax row.2 (JR c0.size c0 s c).label.evaluation) :=
    ⟨Batch1171.inT_child I.inT (by simp), Batch1171.reach_child I.reach (by rw [hch]; simp),
      Batch1171.pr_child I.pr 1 (by simp) (by rw [hch]; simp),
      I.childCall (by omega) (fun _ h => .op9I h r0 hslot'),
      hcoreB, slot_boundedBy (ringChar K) _ _ hcoreB hslot', hs1, hf1⟩
  have G1 := IH1 _ _ I1
  exact ⟨C2ChipReady.op9 hst R.zRow hpubSt ha hth hc harm.symm hleaf.symm R.vcomp hle0 hle1 hls0 hls1
      G0.1 G1.1,
    C2Aligned.op9 hst G0.2 hslot' G1.2⟩

end Steps

/-! ## §D  The induction and the root -/

section Root

variable {z : K} {W D : ℕ} {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}

/-- **The combined evaluation-order induction at the field join**: every node reached by the join
of the root, at a prefix call of the claim's field call tree with bounded inputs, is chip-ready and
aligned. -/
theorem good_of_inpW (C : CtxW (sv := sv) (ax := ax) z (ringChar K) W D t S0 F0) :
    ∀ (n : ℕ) (u : NTree ((State × DTcomp K) × ℕ)) (s f : Noun), u.size ≤ n →
      InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 u s f → GoodW (sv := sv) (ax := ax) z (ringChar K) u s f := by
  intro n
  induction n with
  | zero =>
      intro u s f hu _
      have := Batch1021.ntree_size_pos u
      omega
  | succ n ih =>
    intro u s f hu I
    obtain ⟨row, ch⟩ := u
    have har := (C.row _ I.inT).arity
    simp only [NTree.children, NTree.label] at har
    have IHc : ∀ c ∈ ch, ∀ s' f', InpW (sv := sv) (ax := ax) z (ringChar K) t S0 F0 c s' f' →
        GoodW (sv := sv) (ax := ax) z (ringChar K) c s' f' := fun c hc s' f' I' =>
      ih c s' f' (Batch1021.child_size_le_of_node hu hc) I'
    cases hst : row.1.1 with
    | s0 =>
        rcases ch with _ | ⟨c0, rest⟩
        · exact step_s0W C I hst
        · rw [hst] at har; simp [fanoutComp] at har
    | s1 =>
        rcases ch with _ | ⟨c0, rest⟩
        · exact step_s1W C I hst
        · rw [hst] at har; simp [fanoutComp] at har
    | s2 =>
        rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, rest⟩⟩⟩⟩ <;>
          try (rw [hst] at har; simp [fanoutComp] at har; done)
        exact step_s2W C I hst (IHc c0 (by simp)) (IHc c1 (by simp)) (IHc c2 (by simp))
    | s3 =>
        rcases ch with _ | ⟨c0, _ | ⟨c1, rest⟩⟩ <;>
          try (rw [hst] at har; simp [fanoutComp] at har; done)
        exact step_s3W C I hst (IHc c0 (by simp))
    | s4 =>
        rcases ch with _ | ⟨c0, _ | ⟨c1, rest⟩⟩ <;>
          try (rw [hst] at har; simp [fanoutComp] at har; done)
        exact step_s4W C I hst (IHc c0 (by simp))
    | s5 =>
        rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩ <;>
          try (rw [hst] at har; simp [fanoutComp] at har; done)
        exact step_s5W C I hst (IHc c0 (by simp)) (IHc c1 (by simp))
    | s6 =>
        rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩ <;>
          try (rw [hst] at har; simp [fanoutComp] at har; done)
        exact step_s6W C I hst (IHc c0 (by simp)) (IHc c1 (by simp))
    | s7 =>
        rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩ <;>
          try (rw [hst] at har; simp [fanoutComp] at har; done)
        exact step_s7W C I hst (IHc c0 (by simp)) (IHc c1 (by simp))
    | s8 =>
        rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩ <;>
          try (rw [hst] at har; simp [fanoutComp] at har; done)
        exact step_s8W C I hst (IHc c0 (by simp)) (IHc c1 (by simp))
    | s9 =>
        rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩ <;>
          try (rw [hst] at har; simp [fanoutComp] at har; done)
        exact step_s9W C I hst (IHc c0 (by simp)) (IHc c1 (by simp))
    | cons =>
        rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩ <;>
          try (rw [hst] at har; simp [fanoutComp] at har; done)
        exact step_consW C I hst (IHc c0 (by simp)) (IHc c1 (by simp))

/-- **`root_goodF`** — `Batch1171.root_good` with no honest tree `G`, no honest call, no guarded
run and no `hΛG`: from the package-free context `CtxW` (window `W` under `calls`), bounded root
inputs and the root bindings, the root of the FIELD join is chip-ready and aligned. -/
theorem root_goodF (C : CtxW (sv := sv) (ax := ax) z (ringChar K) W D t S0 F0)
    (bs : BoundedBy (ringChar K) S0) (bf : BoundedBy (ringChar K) F0)
    (hs : bindFP z S0 t.label.1.2.2.1.s) (hf : bindFP z F0 t.label.1.2.2.1.f) :
    C2ChipReady (sv := sv) (ax := ax) z (ringChar K) t S0 F0 ∧ C2Aligned (sv := sv) (ax := ax) (ringChar K) t S0 F0 :=
  good_of_inpW C t.size t S0 F0 le_rfl
    ⟨InTree.here _, InTree.here _, Batch1171.PR.root, ⟨0, by omega, .root⟩, bs, bf, hs, hf⟩

/-- **The claim holds under field semantics at the join's root evaluation** (`root_goodF` composed
with L-B's `holdsF_of_ready`). -/
theorem root_holdsF (C : CtxW (sv := sv) (ax := ax) z (ringChar K) W D t S0 F0)
    (bs : BoundedBy (ringChar K) S0) (bf : BoundedBy (ringChar K) F0)
    (hs : bindFP z S0 t.label.1.2.2.1.s) (hf : bindFP z F0 t.label.1.2.2.1.f) :
    HoldsF (ringChar K) ⟨S0, F0, (JR t.size t S0 F0).label.evaluation⟩ := by
  obtain ⟨hR, hA⟩ := root_goodF C bs bf hs hf
  exact holdsF_of_ready (sv := sv) (ax := ax) hA hR

end Root

end Nock.NockVMROM.Thm54.RootGoodFJoin
