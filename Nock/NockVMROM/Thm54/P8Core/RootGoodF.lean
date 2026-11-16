/-
  Nock/NockVMROM/Thm54/P8Core/RootGoodF.lean

  `Batch1171.root_good` proves `C2ChipReady ∧ C2Aligned` at the root of the decoded C2 join from a
  context `Ctx` that carries the honest generated tree `G` and `hΛG : programLeafBound (airReorder G) ≤ Λ`,
  and from per-node inputs `Inp` that carry an honest call `HonestCall G s f` and a guarded run
  `∃ fuel r, evalGBy q fuel s f = some r`.  This module is the package-free twin's first layer:

  * `CtxF z q W t S0 F0`: `Ctx` with `G` and `hΛG` DELETED and the window an explicit parameter `W`
    with one abstract premise, `LowOrderFree z W` (`∀ d ∈ [1, W], z ^ d ≠ 1`, the noun-free form of the
    size-window event; `not_mem_lowOrderRootSeeds` turns `z ∉ lowOrderRootSeeds W` into it).
  * `InpF`: `Inp` with `call` and `run` DELETED and the window `s.leaves ≤ W ∧ f.leaves ≤ W` carried.
  * the run-free replacements of the shape facts the run used to supply: the formula is a cell
    (record 0's served slot, `slot0F`), the OP0 tail is an atom (the `memBlk` gate `f_t.size = z` +
    `LowOrderFree`), two-record tails are cells (record 1's served slot), the OP4 kid result is an atom
    (`evalV` `sf1_e.size = z` + `LowOrderFree`), the OP9 axis operand is an atom (`f_th.size = z`).
  * the leaf arms OP0 / OP1, the evaluation window of a good LEAF kid from its parent's inputs, and the
    two receipts of the day-1 deliverable: `root_goodF_s2_twoLevel` (the probe R1, promoted) and
    `root_goodF_s4_oneLevel` (the OP4 arm at one row over a leaf kid).

  The window enters in exactly three places, all as the parameter `W`: `CtxF.hW1 : 1 ≤ W`,
  `CtxF.hlow : LowOrderFree z W` and the per-node `InpF.win`; plus the oracles `RecOK z q W` /
  `CensusOK z W` it parametrizes.  No `programLeafBound`, no leaf bound of any tree is named here.

  At the nat-valued join `c2JoinFuel` the OP4
  arm's evaluation is `atom (k+1)` and can leave `BoundedBy q` (`Batch1091.op4_overflow_unbounded`), so
  the internal induction must run over the field twin.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1171Thm54C2InductionPositional

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

namespace Nock.NockVMROM.Thm54.RootGoodF

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.ComputedWindow
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam.Batch1021
open Nock.RedTeam.Batch1090
open Nock.RedTeam.Batch1091
open Nock.RedTeam.Batch1171
open Nock.GlobalCarryRecognizer
open Nock.FieldEmbedding

variable {K : Type} [Field K] [DecidableEq K] [Fintype K] [CharP K (ringChar K)]
variable {sv : MState → ℕ → Noun} {ax : ℕ → ℕ}
set_option quotPrecheck false
local notation "J" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) sv ax

/-! ## §A  The abstract window premise -/

/-- **The window premise** (noun-free): no root of unity of order in `[1, W]` is the seed. -/
def LowOrderFree (z : K) (W : ℕ) : Prop := ∀ d : ℕ, 1 ≤ d → d ≤ W → z ^ d ≠ 1

theorem lowOrderFree_of_not_mem {z : K} {W : ℕ}
    (h : z ∉ SizeWindowCounting.lowOrderRootSeeds (K := K) W) : LowOrderFree z W := by
  intro d hd1 hdW hpow
  apply h
  rw [SizeWindowCounting.lowOrderRootSeeds, Finset.mem_biUnion]
  exact ⟨d, Finset.mem_Icc.mpr ⟨hd1, hdW⟩, (Polynomial.mem_nthRootsFinset (show 0 < d by omega) (1 : K)).mpr hpow⟩

theorem not_mem_of_lowOrderFree {z : K} {W : ℕ} (h : LowOrderFree z W) :
    z ∉ SizeWindowCounting.lowOrderRootSeeds (K := K) W := by
  intro hm
  rw [SizeWindowCounting.lowOrderRootSeeds, Finset.mem_biUnion] at hm
  obtain ⟨d, hd, hroot⟩ := hm
  obtain ⟨hd1, hdW⟩ := Finset.mem_Icc.mp hd
  exact h d hd1 hdW ((Polynomial.mem_nthRootsFinset (show 0 < d by omega) (1 : K)).mp hroot)

/-- Outside the low-order seeds the seed's order exceeds the window. -/
theorem window_lt_orderOf {z : K} {W : ℕ} (hz : z ≠ 0) (h : LowOrderFree z W) : W < orderOf z := by
  have hcard : 0 < Fintype.card K - 1 := by
    have := Fintype.one_lt_card (α := K)
    omega
  have hpos : 0 < orderOf z := by
    rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    exact ⟨Fintype.card K - 1, hcard, FiniteField.pow_card_sub_one_eq_one z hz⟩
  by_contra hle
  exact h (orderOf z) hpos (Nat.le_of_not_lt hle) (pow_orderOf_eq_one z)

/-- **The size-window oracle is derived**: every noun with `≤ W` leaves has its window. -/
theorem sizeWindow_of_lowOrderFree {z : K} {W : ℕ} (hz : z ≠ 0) (hW1 : 1 ≤ W)
    (h : LowOrderFree z W) {n : Noun} (hn : n.leaves ≤ W) : OpcodeSemantics.SizeWindow z n :=
  ⟨by have := window_lt_orderOf hz h; omega, by have := window_lt_orderOf hz h; omega⟩

/-- A windowed noun whose size fingerprint is `z` is an atom. -/
theorem atom_of_size_z {z : K} {W : ℕ} (hz : z ≠ 0) (hW1 : 1 ≤ W) (h : LowOrderFree z W)
    {n : Noun} (hn : n.leaves ≤ W) (hsz : (enc z n).size = z) : ∃ k, n = .atom k :=
  OpcodeSemantics.atom_of_enc_size_eq (sizeWindow_of_lowOrderFree hz hW1 h hn) hsz

/-- `slot` returns a subtree, so it never grows the leaf count (a local copy of
`TraceGen.slot_leaves_le`, kept here so this module imports only the C2 stack). -/
theorem slot_leaves_le' (a : Nat) (n : Noun) :
    ∀ {m : Noun}, Noun.slot a n = some m → m.leaves ≤ n.leaves := by
  induction a, n using Nock.Noun.slot.induct with
  | case1 x => intro m h; simp [Noun.slot] at h
  | case2 n =>
      intro m h
      simp only [Noun.slot] at h
      obtain rfl := Option.some.inj h
      exact le_refl _
  | case3 a n l r hrec ih =>
      intro m h
      have hlr : (Noun.cell l r).leaves ≤ n.leaves := ih hrec
      simp only [Noun.slot, hrec] at h
      split at h
      · obtain rfl := Option.some.inj h
        exact le_trans (leaves_head_le l r) hlr
      · obtain rfl := Option.some.inj h
        exact le_trans (leaves_tail_le l r) hlr
  | case4 a n hno _ =>
      intro m h
      simp only [Noun.slot] at h
      cases hs : Noun.slot ((a + 2) / 2) n with
      | none => simp at h
      | some w =>
        cases w with
        | atom k => simp at h
        | cell l r => exact (hno l r hs).elim

/-! ## §B  The context and the inputs -/

/-- **The package-free context**: `Batch1171.Ctx` with the honest tree `G` and `hΛG` deleted, the
`window` oracle derived, and the window an explicit parameter `W` under `LowOrderFree z W`. -/
structure CtxF (z : K) (q W : ℕ) (t : NTree ((State × DTcomp K) × ℕ)) (S0 F0 : Noun) : Prop where
  hz : z ≠ 0
  hq : 1 < q
  hq12 : 12 ≤ q
  hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q)
  hW1 : 1 ≤ W
  hlow : LowOrderFree z W
  row : ∀ u, InTree t u → RowFacts (ax := ax) z q u
  recs : ∀ u s f, PR t (J t.size t S0 F0) u (J u.size u s f) →
    RecOK z q W u.label (J u.size u s f).label
  census : ∀ u s f, InTree t u → InTree (J t.size t S0 F0) (J u.size u s f) →
    CensusOK z W (J u.size u s f).label

/-- `Batch1171.Ctx`'s `window` field at `CtxF`, as a theorem. -/
theorem CtxF.window {z : K} {q W : ℕ} {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}
    (C : CtxF (sv := sv) (ax := ax) z q W t S0 F0) (u : NTree ((State × DTcomp K) × ℕ)) (s f : Noun) :
    WindowOK z W (J u.size u s f).label :=
  fun _ _ hn => sizeWindow_of_lowOrderFree C.hz C.hW1 C.hlow hn

/-- **Every `Ctx` is a `CtxF`** at the same window, given the window premise. -/
theorem CtxF.of_ctx {z : K} {q Λ : ℕ} {G : NTree (GenComputeRow K)}
    {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}
    (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0) (hlow : LowOrderFree z Λ) :
    CtxF (sv := sv) (ax := ax) z q Λ t S0 F0 :=
  ⟨C.hz, C.hq, C.hq12, C.hcast, C.hΛ1, hlow, C.row, C.recs, C.census⟩

/-- **The inputs carried at a node**: `Batch1171.Inp` without the honest call and the guarded run;
the window of the node's inputs is carried instead. -/
structure InpF (z : K) (q W : ℕ) (t : NTree ((State × DTcomp K) × ℕ)) (S0 F0 : Noun)
    (u : NTree ((State × DTcomp K) × ℕ)) (s f : Noun) : Prop where
  inT : InTree t u
  reach : InTree (J t.size t S0 F0) (J u.size u s f)
  pr : PR t (J t.size t S0 F0) u (J u.size u s f)
  win : s.leaves ≤ W ∧ f.leaves ≤ W
  bs : BoundedBy q s
  bf : BoundedBy q f
  hs : bindFP z s u.label.1.2.2.1.s
  hf : bindFP z f u.label.1.2.2.1.f

/-! ## §C  Run-free shape facts -/

section Shapes

variable {z : K} {q W : ℕ} {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}

/-- **Slot 0 without a run**: the formula's cell shape comes from record 0's served slot. -/
theorem slot0F (C : CtxF (sv := sv) (ax := ax) z q W t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : InpF (sv := sv) (ax := ax) z q W t S0 F0 u s f) :
    ∃ a b, f = .cell a b ∧ bindFP z b u.label.1.2.2.2.f_t ∧ bindFP z a u.label.1.2.2.2.f_h := by
  have R := C.row u I.inT
  have hV := R.vcomp
  have hrec := C.recs u s _ I.pr
  have hj : ((0 : Fin 3) : ℕ) < Nock.Framework.recordCount (J u.size u s f).label.state :=
    recordCount_pos' _
  have hmr1 : traceRec u.label 0 = ⟨u.label.1.2.2.1.f, u.label.1.2.2.2.f_t, 3,
      u.label.1.2.2.1.ln_prev * u.label.1.2.1.α⟩ := hV.2.1
  have h := hrec 0 hj
  rw [J_rec] at h
  simp only [Fin.val_zero] at h
  rw [c2Rec_0, hmr1] at h
  obtain ⟨hslot, hb⟩ := h (enc_eq_of_bind I.hf) I.win.2 I.bf
  cases f with
  | atom k => simp [Noun.slot] at hslot
  | cell a b =>
  simp only [nounTail] at hb
  have hbt : bindFP z b u.label.1.2.2.2.f_t := hb.symm
  refine ⟨a, b, rfl, hbt, ?_⟩
  have hcons : FP.cons z (enc z a) u.label.1.2.2.2.f_t =
      FP.cons z u.label.1.2.2.2.f_h u.label.1.2.2.2.f_t := by
    have h1 : enc z (Noun.cell a b) = u.label.1.2.2.1.f := enc_eq_of_bind I.hf
    rw [enc_cons C.hz, ← hbt] at h1
    rw [h1, hV.1, R.zRow]
  have hne : u.label.1.2.2.2.f_t.size ≠ 0 := by rw [hbt]; exact enc_size_ne_zero C.hz b
  exact (Nock.RedTeam.Batch1023.cons_left_cancel C.hz hne hcons).symm

/-- `Batch1171.head_atom` at `InpF` (census separation; the window is `I.win`). -/
theorem head_atomF (C : CtxF (sv := sv) (ax := ax) z q W t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} {s a b : Noun}
    (I : InpF (sv := sv) (ax := ax) z q W t S0 F0 u s (.cell a b))
    (hcons : u.label.1.1 ≠ .cons) (ha : bindFP z a u.label.1.2.2.2.f_h) :
    a = .atom u.label.1.1.toNat := by
  have R := C.row u I.inT
  have hV := R.vcomp
  have hpc : u.label.1.2.2.1.state ≠ State.cons := by rw [R.pubSt]; exact hcons
  have hst' : u.label.1.2.2.1.state.toNat = u.label.1.1.toNat := by rw [R.pubSt]
  have hfh : u.label.1.2.2.2.f_h = FP.atomFP u.label.1.2.1.z (u.label.1.1.toNat : K) :=
    @Nock.RedTeam.Batch1021.vcomp_f_h_eq_atomFP K _ _ _ _ _ _ _ hV _ hst' hpc
  have henc : enc z a = enc z (.atom u.label.1.1.toNat) := by
    rw [enc_atom, ← ha, hfh, R.zRow]
  have hcen := C.census u s _ I.inT I.reach
  have hmem : P8Census.skeletonUse .opcodeHead a (.atom u.label.1.1.toNat) ∈
      P8Census.skeletonComparisons (K := K) (J u.size u s (.cell a b)).label := by
    rw [J_label_eq]
    have := opcodeHead_mem (K := K) (sv := sv) (ax := ax) u.label.1.1 hcons u.label.2 s (.cell a b)
      ((J u.size u s (.cell a b)).children.map NTree.label)
    simpa [nounHead] using this
  have hsep := hcen _ hmem (by show a.leaves ≤ W; exact (leaves_head_le a b).trans I.win.2)
    (by show (Noun.atom _).leaves ≤ W; rw [leaves_atom]; exact C.hW1)
  have hop : u.label.1.1.toNat < q := by
    have : u.label.1.1.toNat ≤ 9 := by cases u.label.1.1 <;> decide
    have := C.hq12
    omega
  exact noun_eq_of_enc_eq z a _ hsep C.hcast I.bf.1 (by simpa using hop) henc

/-- `Batch1171.tail_bind2` at `InpF`. -/
theorem tail_bind2F (C : CtxF (sv := sv) (ax := ax) z q W t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} {s a c d : Noun}
    (I : InpF (sv := sv) (ax := ax) z q W t S0 F0 u s (.cell a (.cell c d)))
    (hb : bindFP z (.cell c d) u.label.1.2.2.2.f_t)
    (h1 : (1 : ℕ) < Nock.Framework.recordCount u.label.1.1)
    (hrec1 : c2Rec sv ax u.label.1.1 u.label.2 s (.cell a (.cell c d))
      ((J u.size u s (.cell a (.cell c d))).children.map NTree.label) 1 = ⟨.cell c d, c, 2⟩)
    (hmr2 : ∃ ts, u.label.1.2.2.1.mr2 = ⟨u.label.1.2.2.2.f_t, u.label.1.2.2.2.f_th, 2, ts⟩)
    (hcons : FP.cons z u.label.1.2.2.2.f_th u.label.1.2.2.2.f_tt = u.label.1.2.2.2.f_t) :
    bindFP z c u.label.1.2.2.2.f_th ∧ bindFP z d u.label.1.2.2.2.f_tt := by
  have hrec := C.recs u s _ I.pr
  obtain ⟨ts, hmr2⟩ := hmr2
  have h := hrec 1 (by rw [J_label_eq]; exact h1)
  rw [J_rec] at h
  simp only [Fin.val_one] at h
  rw [hrec1] at h
  have hmr : traceRec u.label 1 = u.label.1.2.2.1.mr2 := rfl
  rw [hmr, hmr2] at h
  obtain ⟨-, hc⟩ := h (enc_eq_of_bind hb) ((leaves_tail_le a _).trans I.win.2) I.bf.2
  have hcb : bindFP z c u.label.1.2.2.2.f_th := hc.symm
  refine ⟨hcb, ?_⟩
  have hcc : FP.cons z u.label.1.2.2.2.f_th (enc z d) =
      FP.cons z u.label.1.2.2.2.f_th u.label.1.2.2.2.f_tt := by
    have := enc_eq_of_bind hb
    rw [enc_cons C.hz, ← hcb] at this
    rw [hcons]
    exact this
  have hne : u.label.1.2.2.2.f_th.size ≠ 0 := by rw [hcb]; exact enc_size_ne_zero C.hz c
  exact (Nock.RedTeam.Batch758.cons_right_cancel hne hcc).symm

/-- **A two-record tail is a cell without a run**: record 1's served slot `slot 2 b`. -/
theorem tail_cellF (C : CtxF (sv := sv) (ax := ax) z q W t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} {s a b : Noun}
    (I : InpF (sv := sv) (ax := ax) z q W t S0 F0 u s (.cell a b))
    (hb : bindFP z b u.label.1.2.2.2.f_t)
    (h1 : (1 : ℕ) < Nock.Framework.recordCount u.label.1.1)
    (hrec1 : c2Rec sv ax u.label.1.1 u.label.2 s (.cell a b)
      ((J u.size u s (.cell a b)).children.map NTree.label) 1 = ⟨b, nounHead b, 2⟩)
    (hmr2 : ∃ ts, u.label.1.2.2.1.mr2 = ⟨u.label.1.2.2.2.f_t, u.label.1.2.2.2.f_th, 2, ts⟩) :
    ∃ c d, b = .cell c d := by
  have hrec := C.recs u s _ I.pr
  obtain ⟨ts, hmr2⟩ := hmr2
  have h := hrec 1 (by rw [J_label_eq]; exact h1)
  rw [J_rec] at h
  simp only [Fin.val_one] at h
  rw [hrec1] at h
  have hmr : traceRec u.label 1 = u.label.1.2.2.1.mr2 := rfl
  rw [hmr, hmr2] at h
  obtain ⟨hslot, -⟩ := h (enc_eq_of_bind hb) ((leaves_tail_le a _).trans I.win.2) I.bf.2
  cases b with
  | atom k => simp [Noun.slot] at hslot
  | cell c d => exact ⟨c, d, rfl⟩

/-- The positional child links at a node, unpacked (`Batch1171.link_at'` at `CtxF`). -/
theorem link_atF (C : CtxF (sv := sv) (ax := ax) z q W t S0 F0)
    {row : (State × DTcomp K) × ℕ} {ch : List (NTree ((State × DTcomp K) × ℕ))}
    (hu : InTree t (.node row ch)) (k : Fin 3)
    {c : NTree ((State × DTcomp K) × ℕ)} (hc : ch[(k : ℕ)]? = some c) :
    c.label.1.2.2.1.s = (sfTriple row.1.2.2.1 k).1 ∧
      c.label.1.2.2.1.f = (sfTriple row.1.2.2.1 k).2.1 ∧
      c.label.1.2.2.1.e = (sfTriple row.1.2.2.1 k).2.2 := by
  have h := (C.row _ hu).link k c hc
  exact ⟨congrArg Prod.fst h, congrArg (fun p => p.2.1) h, congrArg (fun p => p.2.2) h⟩

end Shapes

/-! ## §D  The leaf arms -/

section Leaves

variable {z : K} {q W : ℕ} {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}

/-- **OP0 without a run.** -/
theorem step_s0F (C : CtxF (sv := sv) (ax := ax) z q W t S0 F0)
    {row : (State × DTcomp K) × ℕ} {s f : Noun}
    (I : InpF (sv := sv) (ax := ax) z q W t S0 F0 (.node row []) s f) (hst : row.1.1 = .s0) :
    Good (sv := sv) (ax := ax) z q (.node row []) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0F C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row []).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atomF C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hmb : memBlk row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.1
  have hpubSt : row.1.2.2.1.state = .s0 := R.pubSt.trans hst
  simp only [memBlk, hpubSt] at hmb
  -- the tail is an atom: the s0 gate `f_t.size = z` + the window premise (replaces `cases b` on the run)
  have hbL : b.leaves ≤ W := (leaves_tail_le _ b).trans I.win.2
  have hsz : (enc z b).size = z := by
    rw [enc_eq_of_bind hb]; exact hmb.2.2.2.1.trans R.zRow
  obtain ⟨ax', rfl⟩ := atom_of_size_z C.hz C.hW1 C.hlow hbL hsz
  have hax := R.ax0 hst
  have hleaf : row.1.2.2.2.f_t.leaf = (ax' : K) := atomFP_leaf_eq hb
  have haxeq : ax (row.2 + 2) = ax' := hax.1 ax' (by simpa using I.bf.2) hleaf
  have hcastK : ((ax (row.2 + 2) : ℕ) : K) = row.1.2.2.2.f_t.leaf := by rw [haxeq, hleaf]
  have hrec := C.recs _ s _ I.pr
  have h1 : (1 : ℕ) < Nock.Framework.recordCount (NTree.node row []).label.1.1 := by
    simp [hst, Nock.Framework.recordCount]
  have hj : ((1 : Fin 3) : ℕ) < Nock.Framework.recordCount
      (J (NTree.node row []).size (.node row []) s (.cell (.atom 0) (.atom ax'))).label.state := by
    rw [J_label_eq]; exact h1
  have h := hrec 1 hj
  rw [J_rec] at h
  simp only [NTree.label, Fin.val_one] at h
  rw [hst, c2Rec_s0_1] at h
  have hmr : traceRec row 1 = row.1.2.2.1.mr2 := rfl
  rw [hmr, hmb.1] at h
  obtain ⟨hslot, he⟩ := h (enc_eq_of_bind I.hs) I.win.1 I.bs
  refine ⟨C2ChipReady.op0 hst R.zRow hpubSt ha hb he.symm hcastK R.vcomp,
    C2Aligned.op0 (a := ax') hst ?_⟩
  rw [← haxeq]; exact hslot

/-- **OP1** (no run was ever used). -/
theorem step_s1F (C : CtxF (sv := sv) (ax := ax) z q W t S0 F0)
    {row : (State × DTcomp K) × ℕ} {s f : Noun}
    (I : InpF (sv := sv) (ax := ax) z q W t S0 F0 (.node row []) s f) (hst : row.1.1 = .s1) :
    Good (sv := sv) (ax := ax) z q (.node row []) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0F C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row []).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atomF C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s1 := R.pubSt.trans hst
  exact ⟨C2ChipReady.op1 hst R.zRow hpubSt ha hb R.vcomp, C2Aligned.op1 hst⟩

/-- A leaf of a parent `t` (state s0 or s1) is good at any `InpF`. -/
theorem leaf_goodF (C : CtxF (sv := sv) (ax := ax) z q W t S0 F0)
    {row : (State × DTcomp K) × ℕ} (hk : row.1.1 = .s0 ∨ row.1.1 = .s1) {s f : Noun}
    (I : InpF (sv := sv) (ax := ax) z q W t S0 F0 (.node row []) s f) :
    Good (sv := sv) (ax := ax) z q (.node row []) s f := by
  rcases hk with h | h
  · exact step_s0F C I h
  · exact step_s1F C I h

/-- **A good LEAF's evaluation is windowed and bounded by its own inputs** (no call tree): OP0's is a
slot of the subject, OP1's a sub-noun of the formula. -/
theorem leaf_eval_win {row : (State × DTcomp K) × ℕ} {s f : Noun}
    (hG : Good (sv := sv) (ax := ax) z q (.node row []) s f)
    (hs : s.leaves ≤ W) (hf : f.leaves ≤ W) (bs : BoundedBy q s) (bf : BoundedBy q f) :
    (J (NTree.node row []).size (.node row []) s f).label.evaluation.leaves ≤ W ∧
      BoundedBy q (J (NTree.node row []).size (.node row []) s f).label.evaluation := by
  have hA := hG.2
  cases hA with
  | op0 hstate hslot =>
      have hsz : (NTree.node row []).size = 0 + 1 := by simp [NTree.size]
      rw [hsz, J_s0 (sv := sv) (ax := ax) (hstate := hstate)]
      simp only [label_node', c2SkeletonRow_evaluation, c2Evaluation]
      refine ⟨?_, slot_boundedBy q _ _ bs hslot⟩
      exact (slot_leaves_le' _ _ hslot).trans hs
  | op1 hstate =>
      have hsz : (NTree.node row []).size = 0 + 1 := by simp [NTree.size]
      rw [hsz, J_s1 (sv := sv) (ax := ax) (hstate := hstate)]
      simp only [label_node', c2SkeletonRow_evaluation, c2Evaluation, nounTail]
      exact ⟨(leaves_tail_le _ _).trans hf, bf.2⟩

end Leaves

/-! ## §E  The day-1 receipts: OP2 over three leaves (R1, promoted) and OP4 over one leaf -/

section DayOne

variable {z : K} {q W : ℕ} {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}

/-- **`root_goodF` at a two-level OP2 tree** (the probe `sv-probes/R1_RootGoodF2Level.lean`, promoted):
`C2ChipReady ∧ C2Aligned` at the root of `s2[k0, k1, k2]` (each kid s0 or s1) with NO honest call, NO
guarded run and NO honest tree.  Premises beyond the context: the root window (a function of the claim)
and the root bindings.  Child 2's inputs are the kids' evaluations, windowed from the parent's inputs. -/
theorem root_goodF_s2_twoLevel (C : CtxF (sv := sv) (ax := ax) z q W t S0 F0)
    {row r0 r1 r2 : (State × DTcomp K) × ℕ}
    (ht : t = .node row [.node r0 [], .node r1 [], .node r2 []]) (hst : row.1.1 = .s2)
    (hk0 : r0.1.1 = .s0 ∨ r0.1.1 = .s1) (hk1 : r1.1.1 = .s0 ∨ r1.1.1 = .s1)
    (hk2 : r2.1.1 = .s0 ∨ r2.1.1 = .s1)
    (hwin : S0.leaves ≤ W ∧ F0.leaves ≤ W)
    (bs : BoundedBy q S0) (bf : BoundedBy q F0)
    (hs : bindFP z S0 t.label.1.2.2.1.s) (hf : bindFP z F0 t.label.1.2.2.1.f) :
    Good (sv := sv) (ax := ax) z q t S0 F0 := by
  have I : InpF (sv := sv) (ax := ax) z q W t S0 F0 t S0 F0 :=
    ⟨InTree.here _, InTree.here _, PR.root, hwin, bs, bf, hs, hf⟩
  subst ht
  set c0 : NTree ((State × DTcomp K) × ℕ) := .node r0 [] with hc0
  set c1 : NTree ((State × DTcomp K) × ℕ) := .node r1 [] with hc1
  set c2 : NTree ((State × DTcomp K) × ℕ) := .node r2 [] with hc2
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0F C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row [c0, c1, c2]).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atomF C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s2 := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  have hmb : memBlk row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.1
  simp only [memBlk, hpubSt] at hmb
  -- the tail is a cell: record 1's served slot `slot 2 b` (replaces `cases b` on the run)
  obtain ⟨c, d, rfl⟩ : ∃ c d, b = .cell c d := by
    refine tail_cellF C I hb (by simp [NTree.label, hst, Nock.Framework.recordCount]) ?_ ⟨_, hmb.1⟩
    simp only [NTree.label]; rw [hst, c2Rec_s2_1]; rfl
  obtain ⟨m, hsz, hm⟩ := size_succ row [c0, c1, c2]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hm1 : c1.size ≤ m := hm c1 (by simp)
  have hm2 : c2.size ≤ m := hm c2 (by simp)
  have hch : (J (NTree.node row [c0, c1, c2]).size (.node row [c0, c1, c2]) S0
      (.cell (.atom 2) (.cell c d))).children =
      [J c0.size c0 S0 c, J c1.size c1 S0 d,
        J c2.size c2 (J c0.size c0 S0 c).label.evaluation (J c1.size c1 S0 d).label.evaluation] := by
    rw [hsz, J_s2 (sv := sv) (ax := ax) _ _ row c0 c1 c2 hst]
    simp only [NTree.children, nounHead, nounTail]
    rw [J_kid c0 _ _ hm0, J_kid c1 _ _ hm1, J_kid c2 _ _ hm2]
  have hrec1 : c2Rec sv ax row.1.1 row.2 S0 (.cell (.atom 2) (.cell c d))
      ((J (NTree.node row [c0, c1, c2]).size (.node row [c0, c1, c2]) S0
        (.cell (.atom 2) (.cell c d))).children.map NTree.label) 1 = ⟨.cell c d, c, 2⟩ := by
    rw [hst, c2Rec_s2_1]; rfl
  have hzr : row.1.2.1.z = z := R.zRow
  have hcons2 := hmb.2.1
  rw [hzr] at hcons2
  obtain ⟨hc, hd⟩ := tail_bind2F C I hb
    (by simp [NTree.label, hst, Nock.Framework.recordCount]) hrec1 ⟨_, hmb.1⟩ hcons2
  obtain ⟨hls0, hlf0, hle0⟩ := link_atF C I.inT 0 (c := c0) rfl
  obtain ⟨hls1, hlf1, hle1⟩ := link_atF C I.inT 1 (c := c1) rfl
  obtain ⟨hls2, hlf2, hle2⟩ := link_atF C I.inT 2 (c := c2) rfl
  simp only [sfTriple] at hls0 hlf0 hle0 hls1 hlf1 hle1 hls2 hlf2 hle2
  have hs0 : bindFP z S0 c0.label.1.2.2.1.s := by rw [hls0, hev.1]; exact I.hs
  have hf0 : bindFP z c c0.label.1.2.2.1.f := by rw [hlf0, hev.2.1]; exact hc
  have hs1 : bindFP z S0 c1.label.1.2.2.1.s := by rw [hls1, hev.2.2.1]; exact I.hs
  have hf1 : bindFP z d c1.label.1.2.2.1.f := by rw [hlf1, hev.2.2.2.1]; exact hd
  have hcL : c.leaves ≤ W :=
    ((leaves_head_le c d).trans (leaves_tail_le _ _)).trans I.win.2
  have hdL : d.leaves ≤ W :=
    ((leaves_tail_le c d).trans (leaves_tail_le _ _)).trans I.win.2
  have I0 : InpF (sv := sv) (ax := ax) z q W _ S0 _ c0 S0 c :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp),
      pr_child I.pr 0 (by simp) (by rw [hch]; simp), ⟨I.win.1, hcL⟩,
      I.bs, I.bf.2.1, hs0, hf0⟩
  have G0 := leaf_goodF C hk0 I0
  have I1 : InpF (sv := sv) (ax := ax) z q W _ S0 _ c1 S0 d :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp),
      pr_child I.pr 1 (by simp) (by rw [hch]; simp), ⟨I.win.1, hdL⟩,
      I.bs, I.bf.2.2, hs1, hf1⟩
  have G1 := leaf_goodF C hk1 I1
  -- child 2's inputs are the kids' evaluations: windowed from the parent's inputs
  have W0 := leaf_eval_win G0 I.win.1 hcL I.bs I.bf.2.1
  have W1 := leaf_eval_win G1 I.win.1 hdL I.bs I.bf.2.2
  have he0b := kid_e_bind C.hz G0 hs0
  have he1b := kid_e_bind C.hz G1 hs1
  have hs2 : bindFP z (J c0.size c0 S0 c).label.evaluation c2.label.1.2.2.1.s := by
    rw [hls2, hev.2.2.2.2.1, ← hle0]; exact he0b
  have hf2 : bindFP z (J c1.size c1 S0 d).label.evaluation c2.label.1.2.2.1.f := by
    rw [hlf2, hev.2.2.2.2.2.1, ← hle1]; exact he1b
  have I2 : InpF (sv := sv) (ax := ax) z q W _ S0 _ c2 (J c0.size c0 S0 c).label.evaluation
      (J c1.size c1 S0 d).label.evaluation :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp),
      pr_child I.pr 2 (by simp) (by rw [hch]; simp), ⟨W0.1, W1.1⟩, W0.2, W1.2, hs2, hf2⟩
  have G2 := leaf_goodF C hk2 I2
  exact ⟨C2ChipReady.op2 hst R.zRow hpubSt ha hc hd R.vcomp hle0 hle1 hle2 hls0 hls1 hls2
      G0.1 G1.1 G2.1,
    C2Aligned.op2 hst G0.2 G1.2 G2.2⟩

/-- **The OP4 arm at one row** (`s4[k0]`, the kid s0 or s1): no honest call, no guarded run, no
honest tree.  The kid's result is an atom by the chip's own gate `sf1_e.size = z` (`evalV`, s4) and
the window premise, applied to the kid's evaluation, which is windowed by the parent's inputs. -/
theorem root_goodF_s4_oneLevel (C : CtxF (sv := sv) (ax := ax) z q W t S0 F0)
    {row r0 : (State × DTcomp K) × ℕ}
    (ht : t = .node row [.node r0 []]) (hst : row.1.1 = .s4)
    (hk0 : r0.1.1 = .s0 ∨ r0.1.1 = .s1)
    (hwin : S0.leaves ≤ W ∧ F0.leaves ≤ W)
    (bs : BoundedBy q S0) (bf : BoundedBy q F0)
    (hs : bindFP z S0 t.label.1.2.2.1.s) (hf : bindFP z F0 t.label.1.2.2.1.f) :
    Good (sv := sv) (ax := ax) z q t S0 F0 := by
  have I : InpF (sv := sv) (ax := ax) z q W t S0 F0 t S0 F0 :=
    ⟨InTree.here _, InTree.here _, PR.root, hwin, bs, bf, hs, hf⟩
  subst ht
  set c0 : NTree ((State × DTcomp K) × ℕ) := .node r0 [] with hc0
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0F C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row [c0]).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atomF C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s4 := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  obtain ⟨m, hsz, hm⟩ := size_succ row [c0]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hch : (J (NTree.node row [c0]).size (.node row [c0]) S0 (.cell (.atom 4) b)).children =
      [J c0.size c0 S0 b] := by
    rw [hsz, J_s4 (sv := sv) (ax := ax) _ _ row c0 hst]
    simp only [NTree.children, nounTail]
    rw [J_kid c0 S0 b hm0]
  obtain ⟨hls, hlf, hle⟩ := link_atF C I.inT 0 (c := c0) rfl
  simp only [sfTriple] at hls hlf hle
  have hs0 : bindFP z S0 c0.label.1.2.2.1.s := by rw [hls, hev.1]; exact I.hs
  have hf0 : bindFP z b c0.label.1.2.2.1.f := by rw [hlf, hev.2.1]; exact hb
  have hbL : b.leaves ≤ W := (leaves_tail_le _ b).trans I.win.2
  have I0 : InpF (sv := sv) (ax := ax) z q W _ S0 _ c0 S0 b :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp),
      pr_child I.pr 0 (by simp) (by rw [hch]; simp), ⟨I.win.1, hbL⟩, I.bs, I.bf.2, hs0, hf0⟩
  have G0 := leaf_goodF C hk0 I0
  -- the kid's result is an atom: the chip's gate `sf1_e.size = z` + the window premise
  have W0 := leaf_eval_win G0 I.win.1 hbL I.bs I.bf.2
  have he0b := kid_e_bind C.hz G0 hs0
  have hsize : (enc z (J c0.size c0 S0 b).label.evaluation).size = z := by
    rw [enc_eq_of_bind he0b, hle, hev.2.2.1]; exact R.zRow
  obtain ⟨k, hke⟩ := atom_of_size_z C.hz C.hW1 C.hlow W0.1 hsize
  exact ⟨C2ChipReady.op4 hst R.zRow hpubSt ha hb R.vcomp hke hle hls G0.1,
    C2Aligned.op4 hst G0.2⟩

end DayOne

end Nock.NockVMROM.Thm54.RootGoodF
