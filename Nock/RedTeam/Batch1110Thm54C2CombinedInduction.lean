/-
  Nock/RedTeam/Batch1110Thm54C2CombinedInduction.lean

One induction on the S-carrying exec tree in `evalOrder`.  Each node carries (`Inp`): that it is
  reached by the C2 join of the root, an `HonestCall G (s, f)` (the generator's run), a guarded run
  `evalGBy q fuel s f = some r`, bounded inputs, and the subject / formula bindings `bindFP z s row.s`
  / `bindFP z f row.f`.  The context (`Ctx`) carries the per-node trace facts (`RowFacts`: state,
  seed, `V_comp`, arity, `Fcomp` links, the certificate axes), the served-record oracle (`RecOK`), the
  guarded census (`CensusOK`) and the guarded size windows (`WindowOK`) at every REACHED node.  At each
  node:
  * `slot0` — record 1 (`[f, f_t]`, always on) binds the tail; `cons_left_cancel` binds the head;
  * `head_atom` — census separation of `(hd f, atom op)` plus `SVhead` gives the opcode head (gap (i),
    `FormulaShape`); `head_cell` for `cons`;
  * `tail_bind2` / `tail_bind3` — records 2 / 3 bind the structural decompositions;
  * the carried guarded run gives every child's run (OP4 overflow is excluded by the run itself, (iii));

  * OP0 / OP9 served lookups come from `RecOK` (gap (ii): the noun-level `slot`), the certificate axis
    is identified with the formula's by `hcast`;
  * the outputs are `C2ChipReady` and `C2Aligned` at the node (`Good`).

-- the paper
-/
import Nock.RedTeam.Batch1090Thm54C2ReadyFuel
import Nock.RedTeam.Batch1091Thm54C2Alignment
import Nock.RedTeam.Batch1023Thm54S3PairMismatch
import Nock.RedTeam.Batch758Thm54HbindComputeCancel
import Nock.NockVMROM.Thm54.P8Core.Batch1110Thm54C2CombinedInduction

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace Nock.RedTeam.Batch1110

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
open Nock.GlobalCarryRecognizer
open Nock.FieldEmbedding

variable {K : Type} [Field K] [DecidableEq K] [Fintype K] [CharP K (ringChar K)]
variable {sv : MState → ℕ → Noun} {ax : ℕ → ℕ}

set_option quotPrecheck false

local notation "J" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) sv ax

/-! ## §A  The per-node interface -/

/-- The trace's memory record `j` of a compute row (`mr1`, `mr2`, `mr3`). -/
def traceRec (row : (State × DTcomp K) × ℕ) : ℕ → MemRec K
  | 0 => row.1.2.2.1.mr1
  | 1 => row.1.2.2.1.mr2
  | _ => row.1.2.2.1.mr3

/-- **The per-row trace facts** at a node of the S-carrying tree: the row's committed state is the
tree's, the seed, `V_comp`, the arity, the positional `Fcomp` child links, and the certificate axes of
the two served lookups (equal to the record axes in `K`, and below `q`). -/
structure RowFacts (z : K) (q : ℕ) (u : NTree ((State × DTcomp K) × ℕ)) : Prop where
  pubSt : u.label.1.2.2.1.state = u.label.1.1
  zRow : u.label.1.2.1.z = z
  vcomp : Vcomp u.label.1.2.1 u.label.1.2.2.1 u.label.1.2.2.2
  arity : u.children.length = fanoutComp u.label.1.1
  link : ∀ (k : Fin 3) (c : NTree ((State × DTcomp K) × ℕ)), u.children[(k : ℕ)]? = some c →
    (c.label.1.2.2.1.s, c.label.1.2.2.1.f, c.label.1.2.2.1.e) = sfTriple u.label.1.2.2.1 k
  ax0 : u.label.1.1 = .s0 →
    ((ax (u.label.2 + 2) : ℕ) : K) = u.label.1.2.2.2.f_t.leaf ∧ ax (u.label.2 + 2) < q
  ax9 : u.label.1.1 = .s9 →
    ((ax (u.label.2 + 3) : ℕ) : K) = u.label.1.2.2.2.f_th.leaf ∧ ax (u.label.2 + 3) < q

/-- **The served-record oracle** at one C2 node `v` over the trace row `row`: whenever a record's
structural root is bound to the trace record's root (and is in the window and bounded), the
structural child is the noun-level slot of the root at the record's axis, and is bound to the
trace record's child. -/
def RecOK (z : K) (q Λ : ℕ) (row : (State × DTcomp K) × ℕ) (v : ComputeRowSkeleton) : Prop :=
  ∀ (j : Fin 3) (hj : (j : ℕ) < Nock.Framework.recordCount v.state),
    enc z (v.memoryRecord j hj).root = (traceRec row j).root →
    (v.memoryRecord j hj).root.leaves ≤ Λ → BoundedBy q (v.memoryRecord j hj).root →
    Noun.slot (v.memoryRecord j hj).axis (v.memoryRecord j hj).root =
        some (v.memoryRecord j hj).child ∧
      enc z (v.memoryRecord j hj).child = (traceRec row j).child

/-- **The context of the induction**: the tree, its root inputs, the honest generated tree, the
window, and the four families of per-node facts (trace rows, served records, census, windows) at
every node REACHED by the C2 join of the root. -/
structure Ctx (z : K) (q Λ : ℕ) (G : NTree (GenComputeRow K))
    (t : NTree ((State × DTcomp K) × ℕ)) (S0 F0 : Noun) : Prop where
  hz : z ≠ 0
  hq : 1 < q
  hq12 : 12 ≤ q
  hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q)
  hΛ1 : 1 ≤ Λ
  hΛG : programLeafBound (airReorder G) ≤ Λ
  row : ∀ u, InTree t u → RowFacts (ax := ax) z q u
  recs : ∀ u s f, InTree t u → InTree (J t.size t S0 F0) (J u.size u s f) →
    RecOK z q Λ u.label (J u.size u s f).label
  census : ∀ u s f, InTree t u → InTree (J t.size t S0 F0) (J u.size u s f) →
    CensusOK z Λ (J u.size u s f).label
  window : ∀ u s f, InTree t u → InTree (J t.size t S0 F0) (J u.size u s f) →
    WindowOK z Λ (J u.size u s f).label

/-- **The inputs carried at a node** (top-down): reached, honest call, a guarded run, bounded
inputs, and the two input bindings. -/
structure Inp (z : K) (q : ℕ) (G : NTree (GenComputeRow K))
    (t : NTree ((State × DTcomp K) × ℕ)) (S0 F0 : Noun)
    (u : NTree ((State × DTcomp K) × ℕ)) (s f : Noun) : Prop where
  inT : InTree t u
  reach : InTree (J t.size t S0 F0) (J u.size u s f)
  call : HonestCall G s f
  run : ∃ fuel r, evalGBy q fuel s f = some r
  bs : BoundedBy q s
  bf : BoundedBy q f
  hs : bindFP z s u.label.1.2.2.1.s
  hf : bindFP z f u.label.1.2.2.1.f

/-- **The outputs at a node**: chip readiness and alignment. -/
def Good (z : K) (q : ℕ) (u : NTree ((State × DTcomp K) × ℕ)) (s f : Noun) : Prop :=
  C2ChipReady (sv := sv) (ax := ax) z q u s f ∧ C2Aligned (sv := sv) (ax := ax) u s f

/-! ## §B  Small facts -/

theorem J_label_eq (n : ℕ) (t : NTree ((State × DTcomp K) × ℕ)) (s f : Noun) :
    (J n t s f).label =
      c2SkeletonRow sv ax t.label.1.1 t.label.2 s f ((J n t s f).children.map NTree.label) := by
  cases n <;> cases t <;> rfl

/-- The C2 row's record function, proof-free (the body of `c2SkeletonRow.memoryRecord`). -/
def c2Rec (sv' : MState → ℕ → Noun) (ax' : ℕ → ℕ) (st : State) (S : ℕ) (subj formula : Noun)
    (kids : List ComputeRowSkeleton) : ℕ → MemRecSkeleton := fun i =>
  let ft := nounTail formula
  let fth := nounHead ft
  let ftt := nounTail ft
  let ftth := nounHead ftt
  match st, i with
  | _, 0 => ⟨formula, ft, 3⟩
  | .s0, 1 => ⟨subj, c2Evaluation sv' st S formula kids, ax' (S + 2)⟩
  | .s2, 1 | .s5, 1 | .s7, 1 | .s8, 1 | .s9, 1 => ⟨ft, fth, 2⟩
  | .s6, 1 => ⟨ft, fth, 2⟩
  | .s6, 2 => ⟨ftt, ftth, 2⟩
  | .s9, 2 => ⟨(kidSkel kids 0).evaluation, (kidSkel kids 1).formula, ax' (S + 3)⟩
  | _, _ => dummyMemRec

theorem memoryRecord_eq (st : State) (S : ℕ) (subj formula : Noun) (kids : List ComputeRowSkeleton)
    (j : Fin 3) (hj : (j : ℕ) < Nock.Framework.recordCount (c2SkeletonRow sv ax st S subj formula kids).state) :
    (c2SkeletonRow sv ax st S subj formula kids).memoryRecord j hj =
      c2Rec sv ax st S subj formula kids j := by
  rcases j with ⟨j, hj3⟩
  cases st <;> (rcases j with _ | _ | _ | j <;> rfl)

theorem J_rec (n : ℕ) (t : NTree ((State × DTcomp K) × ℕ)) (s f : Noun) (j : Fin 3)
    (hj : (j : ℕ) < Nock.Framework.recordCount (J n t s f).label.state) :
    (J n t s f).label.memoryRecord j hj =
      c2Rec sv ax t.label.1.1 t.label.2 s f ((J n t s f).children.map NTree.label) j := by
  have e := J_label_eq (sv := sv) (ax := ax) n t s f
  simp only [e] at hj ⊢
  exact memoryRecord_eq _ _ _ _ _ j hj

theorem c2Rec_0 (st : State) (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2Rec sv ax st S s f kids 0 = ⟨f, nounTail f, 3⟩ := by
  cases st <;> rfl
theorem c2Rec_s0_1 (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2Rec sv ax .s0 S s f kids 1 = ⟨s, sv .verify_child (S + 2), ax (S + 2)⟩ := rfl
theorem c2Rec_s2_1 (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2Rec sv ax .s2 S s f kids 1 = ⟨nounTail f, nounHead (nounTail f), 2⟩ := rfl
theorem c2Rec_s5_1 (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2Rec sv ax .s5 S s f kids 1 = ⟨nounTail f, nounHead (nounTail f), 2⟩ := rfl
theorem c2Rec_s6_1 (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2Rec sv ax .s6 S s f kids 1 = ⟨nounTail f, nounHead (nounTail f), 2⟩ := rfl
theorem c2Rec_s6_2 (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2Rec sv ax .s6 S s f kids 2 =
      ⟨nounTail (nounTail f), nounHead (nounTail (nounTail f)), 2⟩ := rfl
theorem c2Rec_s7_1 (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2Rec sv ax .s7 S s f kids 1 = ⟨nounTail f, nounHead (nounTail f), 2⟩ := rfl
theorem c2Rec_s8_1 (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2Rec sv ax .s8 S s f kids 1 = ⟨nounTail f, nounHead (nounTail f), 2⟩ := rfl
theorem c2Rec_s9_1 (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2Rec sv ax .s9 S s f kids 1 = ⟨nounTail f, nounHead (nounTail f), 2⟩ := rfl
theorem c2Rec_s9_2 (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    c2Rec sv ax .s9 S s f kids 2 =
      ⟨(kidSkel kids 0).evaluation, (kidSkel kids 1).formula, ax (S + 3)⟩ := rfl

theorem recordCount_pos' (st : State) : (0 : ℕ) < Nock.Framework.recordCount st := by
  cases st <;> decide

theorem enc_size_ne_zero {z : K} (hz : z ≠ 0) (n : Noun) : (enc z n).size ≠ 0 := by
  rw [enc_size]; exact pow_ne_zero _ hz

theorem cell_of_run {q fuel : ℕ} {s f r : Noun} (h : evalGBy q fuel s f = some r) :
    ∃ a b, f = .cell a b := by
  cases fuel with
  | zero => simp [evalGBy] at h
  | succ n =>
      cases f with
      | atom _ => simp [evalGBy] at h
      | cell a b => exact ⟨a, b, rfl⟩

/-- The leaves of a head / tail are at most the cell's. -/
theorem leaves_head_le (a b : Noun) : a.leaves ≤ (Noun.cell a b).leaves := by
  simp [Noun.leaves]

theorem leaves_tail_le (a b : Noun) : b.leaves ≤ (Noun.cell a b).leaves := by
  simp [Noun.leaves]

theorem enc_eq_of_bind {z : K} {n : Noun} {fp : FP K} (h : bindFP z n fp) : enc z n = fp := h.symm

/-! ## §C  The generic first step at every node: the formula is a cell whose tail is bound to
`f_t` and whose head is bound to `f_h` -/

section Generic

variable {z : K} {q Λ : ℕ} {G : NTree (GenComputeRow K)}
  {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}

/-- The node's window: subject and formula within `Λ` (`honestCall_inputs_le`). -/
theorem inp_window (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : Inp (sv := sv) (ax := ax) z q G t S0 F0 u s f) :
    s.leaves ≤ Λ ∧ f.leaves ≤ Λ :=
  ⟨(honestCall_inputs_le I.call).1.trans C.hΛG, (honestCall_inputs_le I.call).2.trans C.hΛG⟩

/-- **Slot 0 at every node**: `f = [a b]`, `enc b = f_t`, `enc a = f_h`. -/
theorem slot0 (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : Inp (sv := sv) (ax := ax) z q G t S0 F0 u s f) :
    ∃ a b, f = .cell a b ∧ bindFP z b u.label.1.2.2.2.f_t ∧ bindFP z a u.label.1.2.2.2.f_h := by
  obtain ⟨fuel, r, hr⟩ := I.run
  obtain ⟨a, b, rfl⟩ := cell_of_run hr
  have R := C.row u I.inT
  have hV := R.vcomp
  have hrec := C.recs u s _ I.inT I.reach
  have hj : ((0 : Fin 3) : ℕ) < Nock.Framework.recordCount (J u.size u s (.cell a b)).label.state :=
    recordCount_pos' _
  have hmr1 : traceRec u.label 0 = ⟨u.label.1.2.2.1.f, u.label.1.2.2.2.f_t, 3,
      u.label.1.2.2.1.ln_prev * u.label.1.2.1.α⟩ := hV.2.1
  have hwin := inp_window C I
  have h := hrec 0 hj
  rw [J_rec] at h
  simp only [Fin.val_zero] at h
  rw [c2Rec_0, hmr1] at h
  simp only [nounTail] at h
  obtain ⟨-, hb⟩ := h (enc_eq_of_bind I.hf) hwin.2 I.bf
  have hbt : bindFP z b u.label.1.2.2.2.f_t := hb.symm
  refine ⟨a, b, rfl, hbt, ?_⟩
  -- `enc [a b] = cons (enc a) (enc b) = f = cons f_h f_t`, left-cancel on `f_t`
  have hcons : FP.cons z (enc z a) u.label.1.2.2.2.f_t = FP.cons z u.label.1.2.2.2.f_h u.label.1.2.2.2.f_t := by
    have h1 : enc z (Noun.cell a b) = u.label.1.2.2.1.f := enc_eq_of_bind I.hf
    rw [enc_cons C.hz, ← hbt] at h1
    rw [h1, hV.1, R.zRow]
  have hne : u.label.1.2.2.2.f_t.size ≠ 0 := by rw [hbt]; exact enc_size_ne_zero C.hz b
  exact (Batch1023.cons_left_cancel C.hz hne hcons).symm

end Generic

/-! ## §D  Head shape, tail bindings, kid helpers -/

section Helpers

variable {z : K} {q Λ : ℕ} {G : NTree (GenComputeRow K)}
  {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}

theorem leaves_atom (k : ℕ) : (Noun.atom k).leaves = 1 := rfl

/-- `skeletonDec` of a C2 row at `f_h` is the formula head. -/
theorem skeletonDec_fh (st : State) (S : ℕ) (s f : Noun) (kids : List ComputeRowSkeleton) :
    P8Census.skeletonDec (c2SkeletonRow sv ax st S s f kids) .f_h = nounHead f := by
  simp [P8Census.skeletonDec, c2SkeletonRow, decActive]

/-- The opcode-head comparison is in every non-`cons` row's census. -/
theorem opcodeHead_mem (st : State) (hst : st ≠ .cons) (S : ℕ) (s f : Noun)
    (kids : List ComputeRowSkeleton) :
    P8Census.skeletonUse .opcodeHead (nounHead f) (.atom st.toNat) ∈
      P8Census.skeletonComparisons (K := K) (c2SkeletonRow sv ax st S s f kids) := by
  have hd := skeletonDec_fh (sv := sv) (ax := ax) st S s f kids
  cases st <;> simp [P8Census.skeletonComparisons, c2SkeletonRow, State.toNat] at hd hst ⊢ <;>
    simp [hd]

/-- **The head at a non-`cons` row is the opcode atom** (census separation + `SVhead`). -/
theorem head_atom (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} {s a b : Noun}
    (I : Inp (sv := sv) (ax := ax) z q G t S0 F0 u s (.cell a b))
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
  have hwin := inp_window C I
  have hmem : P8Census.skeletonUse .opcodeHead a (.atom u.label.1.1.toNat) ∈
      P8Census.skeletonComparisons (K := K) (J u.size u s (.cell a b)).label := by
    rw [J_label_eq]
    have := opcodeHead_mem (K := K) (sv := sv) (ax := ax) u.label.1.1 hcons u.label.2 s (.cell a b)
      ((J u.size u s (.cell a b)).children.map NTree.label)
    simpa [nounHead] using this
  have hsep := hcen _ hmem (by show a.leaves ≤ Λ; exact (leaves_head_le a b).trans hwin.2)
    (by show (Noun.atom _).leaves ≤ Λ; rw [leaves_atom]; exact C.hΛ1)
  have hop : u.label.1.1.toNat < q := by
    have : u.label.1.1.toNat ≤ 9 := by cases u.label.1.1 <;> decide
    have := C.hq12
    omega
  exact noun_eq_of_enc_eq z a _ hsep C.hcast I.bf.1 (by simpa using hop) henc

/-- **The head at a `cons` row is a cell** (`SVhead`'s `headCell`). -/
theorem head_cell (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} {s a b : Noun}
    (I : Inp (sv := sv) (ax := ax) z q G t S0 F0 u s (.cell a b))
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

/-- **Record 1 at a two-record row**: `b = [c d]`, `enc c = f_th`, `enc d = f_tt`. -/
theorem tail_bind2 (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} {s a c d : Noun}
    (I : Inp (sv := sv) (ax := ax) z q G t S0 F0 u s (.cell a (.cell c d)))
    (hb : bindFP z (.cell c d) u.label.1.2.2.2.f_t)
    (h1 : (1 : ℕ) < Nock.Framework.recordCount u.label.1.1)
    (hrec1 : c2Rec sv ax u.label.1.1 u.label.2 s (.cell a (.cell c d))
      ((J u.size u s (.cell a (.cell c d))).children.map NTree.label) 1 = ⟨.cell c d, c, 2⟩)
    (hmr2 : ∃ ts, u.label.1.2.2.1.mr2 = ⟨u.label.1.2.2.2.f_t, u.label.1.2.2.2.f_th, 2, ts⟩)
    (hcons : FP.cons z u.label.1.2.2.2.f_th u.label.1.2.2.2.f_tt = u.label.1.2.2.2.f_t) :
    bindFP z c u.label.1.2.2.2.f_th ∧ bindFP z d u.label.1.2.2.2.f_tt := by
  have hrec := C.recs u s _ I.inT I.reach
  have hwin := inp_window C I
  obtain ⟨ts, hmr2⟩ := hmr2
  have h := hrec 1 (by rw [J_label_eq]; exact h1)
  rw [J_rec] at h
  simp only [Fin.val_one] at h
  rw [hrec1] at h
  have hmr : traceRec u.label 1 = u.label.1.2.2.1.mr2 := rfl
  rw [hmr, hmr2] at h
  obtain ⟨-, hc⟩ := h (enc_eq_of_bind hb) ((leaves_tail_le a _).trans hwin.2) I.bf.2
  have hcb : bindFP z c u.label.1.2.2.2.f_th := hc.symm
  refine ⟨hcb, ?_⟩
  have hcc : FP.cons z u.label.1.2.2.2.f_th (enc z d) =
      FP.cons z u.label.1.2.2.2.f_th u.label.1.2.2.2.f_tt := by
    have := enc_eq_of_bind hb
    rw [enc_cons C.hz, ← hcb] at this
    rw [hcons]
    exact this
  have hne : u.label.1.2.2.2.f_th.size ≠ 0 := by rw [hcb]; exact enc_size_ne_zero C.hz c
  exact (Batch758.cons_right_cancel hne hcc).symm

/-- **Record 2 at an OP6 row**: `d = [e g]`, `enc e = f_tth`, `enc g = f_ttt`. -/
theorem tail_bind3 (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} {s a c e g : Noun}
    (I : Inp (sv := sv) (ax := ax) z q G t S0 F0 u s (.cell a (.cell c (.cell e g))))
    (hd : bindFP z (.cell e g) u.label.1.2.2.2.f_tt)
    (h2 : (2 : ℕ) < Nock.Framework.recordCount u.label.1.1)
    (hrec2 : c2Rec sv ax u.label.1.1 u.label.2 s (.cell a (.cell c (.cell e g)))
      ((J u.size u s (.cell a (.cell c (.cell e g)))).children.map NTree.label) 2 = ⟨.cell e g, e, 2⟩)
    (hmr3 : ∃ ts, u.label.1.2.2.1.mr3 = ⟨u.label.1.2.2.2.f_tt, u.label.1.2.2.2.f_tth, 2, ts⟩)
    (hcons : FP.cons z u.label.1.2.2.2.f_tth u.label.1.2.2.2.f_ttt = u.label.1.2.2.2.f_tt) :
    bindFP z e u.label.1.2.2.2.f_tth ∧ bindFP z g u.label.1.2.2.2.f_ttt := by
  have hrec := C.recs u s _ I.inT I.reach
  have hwin := inp_window C I
  obtain ⟨ts, hmr3⟩ := hmr3
  have h := hrec 2 (by rw [J_label_eq]; exact h2)
  rw [J_rec] at h
  simp only [Fin.val_two] at h
  rw [hrec2] at h
  have hmr : traceRec u.label 2 = u.label.1.2.2.1.mr3 := rfl
  rw [hmr, hmr3] at h
  have hΛd : (Noun.cell e g).leaves ≤ Λ :=
    ((leaves_tail_le c _).trans (leaves_tail_le a _)).trans hwin.2
  obtain ⟨-, he⟩ := h (enc_eq_of_bind hd) hΛd I.bf.2.2
  have heb : bindFP z e u.label.1.2.2.2.f_tth := he.symm
  refine ⟨heb, ?_⟩
  have hcc : FP.cons z u.label.1.2.2.2.f_tth (enc z g) =
      FP.cons z u.label.1.2.2.2.f_tth u.label.1.2.2.2.f_ttt := by
    have := enc_eq_of_bind hd
    rw [enc_cons C.hz, ← heb] at this
    rw [hcons]
    exact this
  have hne : u.label.1.2.2.2.f_tth.size ≠ 0 := by rw [heb]; exact enc_size_ne_zero C.hz e
  exact (Batch758.cons_right_cancel hne hcc).symm

/-- **A good kid's root evaluation binds its `e`.** -/
theorem kid_e_bind (hz : z ≠ 0) {c : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (hG : Good (sv := sv) (ax := ax) z q c s f) (hs : bindFP z s c.label.1.2.2.1.s) :
    bindFP z (J c.size c s f).label.evaluation c.label.1.2.2.1.e :=
  readyF_child_eval_binds hz (c2JoinReadyF_of_chipReady hz hG.1 hs) rfl

/-- **A good kid's evaluation is its guarded run's result.** -/
theorem kid_eval {c : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (hG : Good (sv := sv) (ax := ax) z q c s f) {fuel : ℕ} {r : Noun}
    (hr : evalGBy q fuel s f = some r) {n : ℕ} (hn : c.size ≤ n) :
    (J n c s f).label.evaluation = r :=
  c2_aligned_eval q hG.2 fuel n r hr hn

/-- **A good kid at an honest call has its evaluation inside the window.** -/
theorem kid_eval_le (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {c : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (hG : Good (sv := sv) (ax := ax) z q c s f) (hcall : HonestCall G s f)
    {fuel : ℕ} {r : Noun} (hr : evalGBy q fuel s f = some r) :
    (J c.size c s f).label.evaluation.leaves ≤ Λ := by
  have hg := c2_aligned_genuine (sv := sv) (ax := ax) q hG.2 fuel c.size r hr le_rfl
  have hc : HonestCall G (J c.size c s f).label.subject (J c.size c s f).label.formula := by
    rw [J_subject, J_formula]; exact hcall
  have := (genuine_rows_le_of_honestCall hc hg _ (InTree.here _)).2.2
  exact this.trans C.hΛG

/-- **A good kid's evaluation is bounded** (its run's result). -/
theorem kid_eval_bounded (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {c : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (hG : Good (sv := sv) (ax := ax) z q c s f)
    {fuel : ℕ} {r : Noun} (hr : evalGBy q fuel s f = some r)
    (bs : BoundedBy q s) (bf : BoundedBy q f) :
    BoundedBy q (J c.size c s f).label.evaluation := by
  rw [kid_eval hG hr le_rfl]
  exact evalGBy_bounded C.hq bs bf hr

/-- The join's kid at fuel `m ≥ c.size` is the kid at its own size. -/
theorem J_kid (c : NTree ((State × DTcomp K) × ℕ)) (s f : Noun) {m : ℕ} (hm : c.size ≤ m) :
    J m c s f = J c.size c s f :=
  J_eq_of_le (sv := sv) (ax := ax) c s f le_rfl hm

/-- Reach through a parent join. -/
theorem reach_child {T P k : NTree ComputeRowSkeleton} (hP : InTree T P) (hk : k ∈ P.children) :
    InTree T k :=
  InTree_trans hP (InTree.sub hk (InTree.here _))

theorem inT_child {t u c : NTree ((State × DTcomp K) × ℕ)} (hu : InTree t u) (hc : c ∈ u.children) :
    InTree t c :=
  InTree_trans hu (InTree.sub hc (InTree.here _))

theorem size_succ (row : (State × DTcomp K) × ℕ) (ch : List (NTree ((State × DTcomp K) × ℕ))) :
    ∃ m, (NTree.node row ch).size = m + 1 ∧ ∀ c ∈ ch, c.size ≤ m := by
  refine ⟨(NTree.node row ch).size - 1, ?_, ?_⟩
  · have := Batch1021.ntree_size_pos (NTree.node row ch); omega
  · intro c hc
    have hpos := Batch1021.ntree_size_pos (NTree.node row ch)
    have hk : (NTree.node row ch).size ≤ (NTree.node row ch).size - 1 + 1 := by omega
    exact Batch1021.child_size_le_of_node hk hc

end Helpers

/-! ## §E  The leaves: OP0 and OP1 -/

section Leaves

variable {z : K} {q Λ : ℕ} {G : NTree (GenComputeRow K)}
  {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}

theorem natCast_inj_of_lt' (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0) {x y : ℕ}
    (hx : x < q) (hy : y < q) (h : (x : K) = (y : K)) : x = y :=
  C.hcast (Set.mem_Iio.2 hx) (Set.mem_Iio.2 hy) h

theorem atomFP_leaf_eq {z : K} {n : ℕ} {fp : FP K} (h : bindFP z (.atom n) fp) : fp.leaf = (n : K) := by
  rw [h, enc_atom]; rfl

/-- **OP0.** -/
theorem step_s0 (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {row : (State × DTcomp K) × ℕ} {s f : Noun}
    (I : Inp (sv := sv) (ax := ax) z q G t S0 F0 (.node row []) s f) (hst : row.1.1 = .s0) :
    Good (sv := sv) (ax := ax) z q (.node row []) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0 C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row []).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atom C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  obtain ⟨fuel, r, hr⟩ := I.run
  cases fuel with
  | zero => simp [evalGBy] at hr
  | succ n =>
  cases b with
  | cell _ _ => simp [evalGBy] at hr
  | atom ax' =>
  have hax := R.ax0 hst
  have hleaf : row.1.2.2.2.f_t.leaf = (ax' : K) := atomFP_leaf_eq hb
  have haxeq : ax (row.2 + 2) = ax' :=
    natCast_inj_of_lt' C hax.2 (by simpa using I.bf.2) (by rw [← hleaf]; exact hax.1)
  have hwin := inp_window C I
  have hrec := C.recs _ s _ I.inT I.reach
  have h1 : (1 : ℕ) < Nock.Framework.recordCount (NTree.node row []).label.1.1 := by
    simp [hst, Nock.Framework.recordCount]
  have hj : ((1 : Fin 3) : ℕ) < Nock.Framework.recordCount
      (J (NTree.node row []).size (.node row []) s (.cell (.atom 0) (.atom ax'))).label.state := by
    rw [J_label_eq]; exact h1
  have hmb : memBlk row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.1
  have hpubSt : row.1.2.2.1.state = .s0 := R.pubSt.trans hst
  simp only [memBlk, hpubSt] at hmb
  have h := hrec 1 hj
  rw [J_rec] at h
  simp only [NTree.label, Fin.val_one] at h
  rw [hst, c2Rec_s0_1] at h
  have hmr : traceRec row 1 = row.1.2.2.1.mr2 := rfl
  rw [hmr, hmb.1] at h
  obtain ⟨hslot, he⟩ := h (enc_eq_of_bind I.hs) hwin.1 I.bs
  refine ⟨C2ChipReady.op0 hst R.zRow hpubSt ha hb he.symm hax.1 R.vcomp,
    C2Aligned.op0 (a := ax') hst ?_⟩
  rw [← haxeq]; exact hslot

/-- **OP1.** -/
theorem step_s1 (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {row : (State × DTcomp K) × ℕ} {s f : Noun}
    (I : Inp (sv := sv) (ax := ax) z q G t S0 F0 (.node row []) s f) (hst : row.1.1 = .s1) :
    Good (sv := sv) (ax := ax) z q (.node row []) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0 C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row []).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atom C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s1 := R.pubSt.trans hst
  exact ⟨C2ChipReady.op1 hst R.zRow hpubSt ha hb R.vcomp, C2Aligned.op1 hst⟩

end Leaves

/-! ## §F  Internal nodes with structural children: OP3, OP4, cons -/

section Internal1

variable {z : K} {q Λ : ℕ} {G : NTree (GenComputeRow K)}
  {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}

theorem kid_genuine {c : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (hG : Good (sv := sv) (ax := ax) z q c s f) {fuel : ℕ} {r : Noun}
    (hr : evalGBy q fuel s f = some r) : GenuineSkel (J c.size c s f) :=
  c2_aligned_genuine q hG.2 fuel c.size r hr le_rfl

/-- The `i`-th positional child link, unpacked. -/
theorem link_at (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {u : NTree ((State × DTcomp K) × ℕ)} (hu : InTree t u) (k : Fin 3)
    {c : NTree ((State × DTcomp K) × ℕ)} (hc : u.children[(k : ℕ)]? = some c) :
    (c.label.1.2.2.1.s, c.label.1.2.2.1.f, c.label.1.2.2.1.e) = sfTriple u.label.1.2.2.1 k :=
  (C.row u hu).link k c hc

/-- The same at a node `row`, unpacked. -/
theorem link_at' (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {row : (State × DTcomp K) × ℕ} {ch : List (NTree ((State × DTcomp K) × ℕ))}
    (hu : InTree t (.node row ch)) (k : Fin 3)
    {c : NTree ((State × DTcomp K) × ℕ)} (hc : ch[(k : ℕ)]? = some c) :
    c.label.1.2.2.1.s = (sfTriple row.1.2.2.1 k).1 ∧
      c.label.1.2.2.1.f = (sfTriple row.1.2.2.1 k).2.1 ∧
      c.label.1.2.2.1.e = (sfTriple row.1.2.2.1 k).2.2 := by
  have h := (C.row _ hu).link k c hc
  exact ⟨congrArg Prod.fst h, congrArg (fun p => p.2.1) h, congrArg (fun p => p.2.2) h⟩

/-- **OP3.** -/
theorem step_s3 (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {row : (State × DTcomp K) × ℕ} {c0 : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : Inp (sv := sv) (ax := ax) z q G t S0 F0 (.node row [c0]) s f) (hst : row.1.1 = .s3)
    (IH : ∀ s' f', Inp (sv := sv) (ax := ax) z q G t S0 F0 c0 s' f' →
      Good (sv := sv) (ax := ax) z q c0 s' f') :
    Good (sv := sv) (ax := ax) z q (.node row [c0]) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0 C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row [c0]).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atom C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s3 := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  obtain ⟨m, hsz, hm⟩ := size_succ row [c0]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hch : (J (NTree.node row [c0]).size (.node row [c0]) s (.cell (.atom 3) b)).children =
      [J c0.size c0 s b] := by
    rw [hsz, J_s3 (sv := sv) (ax := ax) _ _ row c0 hst]
    simp only [NTree.children, nounTail]
    rw [J_kid c0 s b hm0]
  obtain ⟨fuel, r, hr⟩ := I.run
  cases fuel with
  | zero => simp [evalGBy] at hr
  | succ n =>
  simp only [evalGBy, Option.map_eq_some_iff] at hr
  obtain ⟨r0, hr0, -⟩ := hr
  obtain ⟨hls, hlf, hle⟩ := link_at' C I.inT 0 (c := c0) rfl
  simp only [sfTriple] at hls hlf hle
  have hs0 : bindFP z s c0.label.1.2.2.1.s := by rw [hls, hev.1]; exact I.hs
  have hf0 : bindFP z b c0.label.1.2.2.1.f := by rw [hlf, hev.2.1]; exact hb
  have hin : KidInputs .s3 s (.cell (.atom 3) b) ([J c0.size c0 s b].map NTree.label) := by
    simp [KidInputs, J_subject, J_formula, tl_cell]
  have hshape : FormulaShape .s3 (.cell (.atom 3) b) := ⟨b, rfl⟩
  have hcall0 : HonestCall G s b := by
    have h := honestCall_kid I.call hshape hin 0 (J c0.size c0 s b)
      (by simp [evalOrder, airNeedsSwap]) (fun j _ hj _ => absurd hj (by omega))
    rwa [J_subject, J_formula] at h
  have I0 : Inp (sv := sv) (ax := ax) z q G t S0 F0 c0 s b :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp), hcall0, ⟨n, r0, hr0⟩,
      I.bs, I.bf.2, hs0, hf0⟩
  have G0 := IH s b I0
  have hwinN : OpcodeSemantics.SizeWindow z (J c0.size c0 s b).label.evaluation := by
    have hW := C.window _ s _ I.inT I.reach
    apply hW
    · rw [J_label_eq]
      simp only [NTree.label, hst, hch]
      simp [SizeWindowCounting.requiredSizeWindowNouns, c2SkeletonRow, P8Census.skeletonSubformula,
        fanoutComp]
      rfl
    · exact kid_eval_le C G0 hcall0 hr0
  exact ⟨C2ChipReady.op3 hst R.zRow hpubSt ha hb R.vcomp hwinN hle hls G0.1,
    C2Aligned.op3 hst G0.2⟩

/-- **OP4.** -/
theorem step_s4 (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {row : (State × DTcomp K) × ℕ} {c0 : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : Inp (sv := sv) (ax := ax) z q G t S0 F0 (.node row [c0]) s f) (hst : row.1.1 = .s4)
    (IH : ∀ s' f', Inp (sv := sv) (ax := ax) z q G t S0 F0 c0 s' f' →
      Good (sv := sv) (ax := ax) z q c0 s' f') :
    Good (sv := sv) (ax := ax) z q (.node row [c0]) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0 C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row [c0]).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atom C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s4 := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  obtain ⟨m, hsz, hm⟩ := size_succ row [c0]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hch : (J (NTree.node row [c0]).size (.node row [c0]) s (.cell (.atom 4) b)).children =
      [J c0.size c0 s b] := by
    rw [hsz, J_s4 (sv := sv) (ax := ax) _ _ row c0 hst]
    simp only [NTree.children, nounTail]
    rw [J_kid c0 s b hm0]
  obtain ⟨fuel, r, hr⟩ := I.run
  cases fuel with
  | zero => simp [evalGBy] at hr
  | succ n =>
  simp only [evalGBy, Option.bind_eq_some_iff] at hr
  obtain ⟨r0, hr0, hlus⟩ := hr
  obtain ⟨k, rfl⟩ : ∃ k, r0 = .atom k := by
    cases r0 with
    | atom k => exact ⟨k, rfl⟩
    | cell _ _ => simp [lusGBy] at hlus
  obtain ⟨hls, hlf, hle⟩ := link_at' C I.inT 0 (c := c0) rfl
  simp only [sfTriple] at hls hlf hle
  have hs0 : bindFP z s c0.label.1.2.2.1.s := by rw [hls, hev.1]; exact I.hs
  have hf0 : bindFP z b c0.label.1.2.2.1.f := by rw [hlf, hev.2.1]; exact hb
  have hin : KidInputs .s4 s (.cell (.atom 4) b) ([J c0.size c0 s b].map NTree.label) := by
    simp [KidInputs, J_subject, J_formula, tl_cell]
  have hshape : FormulaShape .s4 (.cell (.atom 4) b) := ⟨b, rfl⟩
  have hcall0 : HonestCall G s b := by
    have h := honestCall_kid I.call hshape hin 0 (J c0.size c0 s b)
      (by simp [evalOrder, airNeedsSwap]) (fun j _ hj _ => absurd hj (by omega))
    rwa [J_subject, J_formula] at h
  have I0 : Inp (sv := sv) (ax := ax) z q G t S0 F0 c0 s b :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp), hcall0, ⟨n, _, hr0⟩,
      I.bs, I.bf.2, hs0, hf0⟩
  have G0 := IH s b I0
  have hke : (J c0.size c0 s b).label.evaluation = .atom k := kid_eval G0 hr0 le_rfl
  exact ⟨C2ChipReady.op4 hst R.zRow hpubSt ha hb R.vcomp hke hle hls G0.1,
    C2Aligned.op4 hst G0.2⟩

/-- **cons.** -/
theorem step_cons (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : Inp (sv := sv) (ax := ax) z q G t S0 F0 (.node row [c0, c1]) s f) (hst : row.1.1 = .cons)
    (IH0 : ∀ s' f', Inp (sv := sv) (ax := ax) z q G t S0 F0 c0 s' f' →
      Good (sv := sv) (ax := ax) z q c0 s' f')
    (IH1 : ∀ s' f', Inp (sv := sv) (ax := ax) z q G t S0 F0 c1 s' f' →
      Good (sv := sv) (ax := ax) z q c1 s' f') :
    Good (sv := sv) (ax := ax) z q (.node row [c0, c1]) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0 C I
  have R := C.row _ I.inT
  obtain ⟨lh, lt, rfl⟩ := head_cell C I hst ha
  have hpubSt : row.1.2.2.1.state = .cons := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  obtain ⟨m, hsz, hm⟩ := size_succ row [c0, c1]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hm1 : c1.size ≤ m := hm c1 (by simp)
  have hch : (J (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
      (.cell (.cell lh lt) b)).children = [J c0.size c0 s (.cell lh lt), J c1.size c1 s b] := by
    rw [hsz, J_cons (sv := sv) (ax := ax) _ _ row c0 c1 hst]
    simp only [NTree.children, nounHead, nounTail]
    rw [J_kid c0 _ _ hm0, J_kid c1 _ _ hm1]
  obtain ⟨fuel, r, hr⟩ := I.run
  cases fuel with
  | zero => simp [evalGBy] at hr
  | succ n =>
  simp only [evalGBy] at hr
  obtain ⟨l, hl⟩ : ∃ l, evalGBy q n s (.cell lh lt) = some l := by
    cases h : evalGBy q n s (.cell lh lt) with
    | none => rw [h] at hr; simp at hr
    | some l => exact ⟨l, rfl⟩
  obtain ⟨r', hr'⟩ : ∃ r', evalGBy q n s b = some r' := by
    cases h : evalGBy q n s b with
    | none => rw [hl, h] at hr; simp at hr
    | some r' => exact ⟨r', rfl⟩
  obtain ⟨hls0, hlf0, hle0⟩ := link_at' C I.inT 0 (c := c0) rfl
  obtain ⟨hls1, hlf1, hle1⟩ := link_at' C I.inT 1 (c := c1) rfl
  simp only [sfTriple] at hls0 hlf0 hle0 hls1 hlf1 hle1
  have hs0 : bindFP z s c0.label.1.2.2.1.s := by rw [hls0, hev.1]; exact I.hs
  have hf0 : bindFP z (.cell lh lt) c0.label.1.2.2.1.f := by rw [hlf0, hev.2.1]; exact ha
  have hs1 : bindFP z s c1.label.1.2.2.1.s := by rw [hls1, hev.2.2.1]; exact I.hs
  have hf1 : bindFP z b c1.label.1.2.2.1.f := by rw [hlf1, hev.2.2.2.1]; exact hb
  have hin : KidInputs .cons s (.cell (.cell lh lt) b)
      ([J c0.size c0 s (.cell lh lt), J c1.size c1 s b].map NTree.label) := by
    simp [KidInputs, J_subject, J_formula, hd_cell, tl_cell]
  have hshape : FormulaShape .cons (.cell (.cell lh lt) b) := ⟨lh, lt, b, rfl⟩
  have hcall0 : HonestCall G s (.cell lh lt) := by
    have h := honestCall_kid I.call hshape hin 0 (J c0.size c0 s (.cell lh lt))
      (by simp [evalOrder, airNeedsSwap]) (fun j _ hj _ => absurd hj (by omega))
    rwa [J_subject, J_formula] at h
  have I0 : Inp (sv := sv) (ax := ax) z q G t S0 F0 c0 s (.cell lh lt) :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp), hcall0, ⟨n, l, hl⟩,
      I.bs, I.bf.1, hs0, hf0⟩
  have G0 := IH0 _ _ I0
  have gen0 := kid_genuine G0 hl
  have hcall1 : HonestCall G s b := by
    have h := honestCall_kid I.call hshape hin 1 (J c1.size c1 s b)
      (by simp [evalOrder, airNeedsSwap])
      (by
        intro j k' hj hk'
        rcases j with _ | j
        · simp [evalOrder, airNeedsSwap] at hk'; subst hk'; exact gen0
        · omega)
    rwa [J_subject, J_formula] at h
  have I1 : Inp (sv := sv) (ax := ax) z q G t S0 F0 c1 s b :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp), hcall1, ⟨n, r', hr'⟩,
      I.bs, I.bf.2, hs1, hf1⟩
  have G1 := IH1 _ _ I1
  exact ⟨C2ChipReady.cons hst R.zRow hpubSt ha hb R.vcomp hle0 hle1 hls0 hls1 G0.1 G1.1,
    C2Aligned.cons hst G0.2 G1.2⟩

end Internal1

/-! ## §G  Internal nodes with two records: OP5, OP2, OP7, OP8 -/

section Internal2

variable {z : K} {q Λ : ℕ} {G : NTree (GenComputeRow K)}
  {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}

/-- The common prelude at a two-record opcode row `op ∈ {2,5,7,8}`: head, tail shape, the two
decomposition bindings, the links. -/
theorem two_rec_prelude (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {row : (State × DTcomp K) × ℕ} {ch : List (NTree ((State × DTcomp K) × ℕ))} {s c d : Noun}
    {op : ℕ}
    (I : Inp (sv := sv) (ax := ax) z q G t S0 F0 (.node row ch) s (.cell (.atom op) (.cell c d)))
    (hb : bindFP z (.cell c d) row.1.2.2.2.f_t)
    (hrec1 : c2Rec sv ax row.1.1 row.2 s (.cell (.atom op) (.cell c d))
      ((J (NTree.node row ch).size (.node row ch) s (.cell (.atom op) (.cell c d))).children.map
        NTree.label) 1 = ⟨.cell c d, c, 2⟩)
    (h1 : (1 : ℕ) < Nock.Framework.recordCount row.1.1)
    (hmr2 : ∃ ts, row.1.2.2.1.mr2 = ⟨row.1.2.2.2.f_t, row.1.2.2.2.f_th, 2, ts⟩)
    (hcons : FP.cons row.1.2.1.z row.1.2.2.2.f_th row.1.2.2.2.f_tt = row.1.2.2.2.f_t) :
    bindFP z c row.1.2.2.2.f_th ∧ bindFP z d row.1.2.2.2.f_tt := by
  have hz' : row.1.2.1.z = z := (C.row _ I.inT).zRow
  rw [hz'] at hcons
  exact tail_bind2 C I hb h1 hrec1 hmr2 hcons

/-- **OP5.** -/
theorem step_s5 (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : Inp (sv := sv) (ax := ax) z q G t S0 F0 (.node row [c0, c1]) s f) (hst : row.1.1 = .s5)
    (IH0 : ∀ s' f', Inp (sv := sv) (ax := ax) z q G t S0 F0 c0 s' f' →
      Good (sv := sv) (ax := ax) z q c0 s' f')
    (IH1 : ∀ s' f', Inp (sv := sv) (ax := ax) z q G t S0 F0 c1 s' f' →
      Good (sv := sv) (ax := ax) z q c1 s' f') :
    Good (sv := sv) (ax := ax) z q (.node row [c0, c1]) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0 C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row [c0, c1]).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atom C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s5 := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  have hmb : memBlk row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.1
  simp only [memBlk, hpubSt] at hmb
  obtain ⟨fuel, r, hr⟩ := I.run
  cases fuel with
  | zero => simp [evalGBy] at hr
  | succ n =>
  obtain ⟨c, d, rfl⟩ : ∃ c d, b = .cell c d := by
    cases b with
    | atom _ => simp [evalGBy] at hr
    | cell c d => exact ⟨c, d, rfl⟩
  simp only [evalGBy] at hr
  obtain ⟨e0, he0⟩ : ∃ e0, evalGBy q n s c = some e0 := by
    cases h : evalGBy q n s c with
    | none => rw [h] at hr; simp at hr
    | some e0 => exact ⟨e0, rfl⟩
  obtain ⟨e1, he1⟩ : ∃ e1, evalGBy q n s d = some e1 := by
    cases h : evalGBy q n s d with
    | none => rw [he0, h] at hr; simp at hr
    | some e1 => exact ⟨e1, rfl⟩
  obtain ⟨m, hsz, hm⟩ := size_succ row [c0, c1]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hm1 : c1.size ≤ m := hm c1 (by simp)
  have hch : (J (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
      (.cell (.atom 5) (.cell c d))).children = [J c0.size c0 s c, J c1.size c1 s d] := by
    rw [hsz, J_s5 (sv := sv) (ax := ax) _ _ row c0 c1 hst]
    simp only [NTree.children, nounHead, nounTail]
    rw [J_kid c0 _ _ hm0, J_kid c1 _ _ hm1]
  have hrec1 : c2Rec sv ax row.1.1 row.2 s (.cell (.atom 5) (.cell c d))
      ((J (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
        (.cell (.atom 5) (.cell c d))).children.map NTree.label) 1 = ⟨.cell c d, c, 2⟩ := by
    rw [hst, c2Rec_s5_1]; rfl
  obtain ⟨hc, hd⟩ := two_rec_prelude C I hb hrec1 (by rw [hst]; decide) ⟨_, hmb.1⟩ hmb.2.1
  obtain ⟨hls0, hlf0, hle0⟩ := link_at' C I.inT 0 (c := c0) rfl
  obtain ⟨hls1, hlf1, hle1⟩ := link_at' C I.inT 1 (c := c1) rfl
  simp only [sfTriple] at hls0 hlf0 hle0 hls1 hlf1 hle1
  have hs0 : bindFP z s c0.label.1.2.2.1.s := by rw [hls0, hev.1]; exact I.hs
  have hf0 : bindFP z c c0.label.1.2.2.1.f := by rw [hlf0, hev.2.1]; exact hc
  have hs1 : bindFP z s c1.label.1.2.2.1.s := by rw [hls1, hev.2.2.1]; exact I.hs
  have hf1 : bindFP z d c1.label.1.2.2.1.f := by rw [hlf1, hev.2.2.2.1]; exact hd
  have hin : KidInputs .s5 s (.cell (.atom 5) (.cell c d))
      ([J c0.size c0 s c, J c1.size c1 s d].map NTree.label) := by
    simp [KidInputs, J_subject, J_formula, hd_cell, tl_cell]
  have hshape : FormulaShape .s5 (.cell (.atom 5) (.cell c d)) := ⟨c, d, rfl⟩
  have hcall0 : HonestCall G s c := by
    have h := honestCall_kid I.call hshape hin 0 (J c0.size c0 s c)
      (by simp [evalOrder, airNeedsSwap]) (fun j _ hj _ => absurd hj (by omega))
    rwa [J_subject, J_formula] at h
  have I0 : Inp (sv := sv) (ax := ax) z q G t S0 F0 c0 s c :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp), hcall0, ⟨n, e0, he0⟩,
      I.bs, I.bf.2.1, hs0, hf0⟩
  have G0 := IH0 _ _ I0
  have gen0 := kid_genuine G0 he0
  have hcall1 : HonestCall G s d := by
    have h := honestCall_kid I.call hshape hin 1 (J c1.size c1 s d)
      (by simp [evalOrder, airNeedsSwap])
      (by
        intro j k' hj hk'
        rcases j with _ | j
        · simp [evalOrder, airNeedsSwap] at hk'; subst hk'; exact gen0
        · omega)
    rwa [J_subject, J_formula] at h
  have I1 : Inp (sv := sv) (ax := ax) z q G t S0 F0 c1 s d :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp), hcall1, ⟨n, e1, he1⟩,
      I.bs, I.bf.2.2, hs1, hf1⟩
  have G1 := IH1 _ _ I1
  have hfaith : OpcodeSemantics.PairFaithful z q (J c0.size c0 s c).label.evaluation
      (J c1.size c1 s d).label.evaluation := by
    have hcen := C.census _ s _ I.inT I.reach
    refine ⟨hcen (P8Census.skeletonUse .equalityOperand (J c0.size c0 s c).label.evaluation
        (J c1.size c1 s d).label.evaluation) ?_
        (kid_eval_le C G0 hcall0 he0) (kid_eval_le C G1 hcall1 he1),
      kid_eval_bounded C G0 he0 I.bs I.bf.2.1, kid_eval_bounded C G1 he1 I.bs I.bf.2.2⟩
    rw [J_label_eq]
    simp only [NTree.label, hst, hch]
    simp [P8Census.skeletonComparisons, c2SkeletonRow, P8Census.skeletonSubformula, fanoutComp,
      P8Census.skeletonUse]
    exact ⟨rfl, rfl⟩
  exact ⟨C2ChipReady.op5 hst R.zRow hpubSt ha hc hd R.vcomp C.hcast hfaith hle0 hle1 hls0 hls1
      G0.1 G1.1,
    C2Aligned.op5 hst G0.2 G1.2⟩

/-- **OP2.** -/
theorem step_s2 (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {row : (State × DTcomp K) × ℕ} {c0 c1 c2 : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : Inp (sv := sv) (ax := ax) z q G t S0 F0 (.node row [c0, c1, c2]) s f) (hst : row.1.1 = .s2)
    (IH0 : ∀ s' f', Inp (sv := sv) (ax := ax) z q G t S0 F0 c0 s' f' →
      Good (sv := sv) (ax := ax) z q c0 s' f')
    (IH1 : ∀ s' f', Inp (sv := sv) (ax := ax) z q G t S0 F0 c1 s' f' →
      Good (sv := sv) (ax := ax) z q c1 s' f')
    (IH2 : ∀ s' f', Inp (sv := sv) (ax := ax) z q G t S0 F0 c2 s' f' →
      Good (sv := sv) (ax := ax) z q c2 s' f') :
    Good (sv := sv) (ax := ax) z q (.node row [c0, c1, c2]) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0 C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row [c0, c1, c2]).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atom C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s2 := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  have hmb : memBlk row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.1
  simp only [memBlk, hpubSt] at hmb
  obtain ⟨fuel, r, hr⟩ := I.run
  cases fuel with
  | zero => simp [evalGBy] at hr
  | succ n =>
  obtain ⟨c, d, rfl⟩ : ∃ c d, b = .cell c d := by
    cases b with
    | atom _ => simp [evalGBy] at hr
    | cell c d => exact ⟨c, d, rfl⟩
  simp only [evalGBy] at hr
  obtain ⟨e0, he0⟩ : ∃ e0, evalGBy q n s c = some e0 := by
    cases h : evalGBy q n s c with
    | none => rw [h] at hr; simp at hr
    | some e0 => exact ⟨e0, rfl⟩
  obtain ⟨e1, he1⟩ : ∃ e1, evalGBy q n s d = some e1 := by
    cases h : evalGBy q n s d with
    | none => rw [he0, h] at hr; simp at hr
    | some e1 => exact ⟨e1, rfl⟩
  rw [he0, he1] at hr
  obtain ⟨m, hsz, hm⟩ := size_succ row [c0, c1, c2]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hm1 : c1.size ≤ m := hm c1 (by simp)
  have hm2 : c2.size ≤ m := hm c2 (by simp)
  have hch : (J (NTree.node row [c0, c1, c2]).size (.node row [c0, c1, c2]) s
      (.cell (.atom 2) (.cell c d))).children =
      [J c0.size c0 s c, J c1.size c1 s d,
        J c2.size c2 (J c0.size c0 s c).label.evaluation (J c1.size c1 s d).label.evaluation] := by
    rw [hsz, J_s2 (sv := sv) (ax := ax) _ _ row c0 c1 c2 hst]
    simp only [NTree.children, nounHead, nounTail]
    rw [J_kid c0 _ _ hm0, J_kid c1 _ _ hm1, J_kid c2 _ _ hm2]
  have hrec1 : c2Rec sv ax row.1.1 row.2 s (.cell (.atom 2) (.cell c d))
      ((J (NTree.node row [c0, c1, c2]).size (.node row [c0, c1, c2]) s
        (.cell (.atom 2) (.cell c d))).children.map NTree.label) 1 = ⟨.cell c d, c, 2⟩ := by
    rw [hst, c2Rec_s2_1]; rfl
  obtain ⟨hc, hd⟩ := two_rec_prelude C I hb hrec1 (by rw [hst]; decide) ⟨_, hmb.1⟩ hmb.2.1
  obtain ⟨hls0, hlf0, hle0⟩ := link_at' C I.inT 0 (c := c0) rfl
  obtain ⟨hls1, hlf1, hle1⟩ := link_at' C I.inT 1 (c := c1) rfl
  obtain ⟨hls2, hlf2, hle2⟩ := link_at' C I.inT 2 (c := c2) rfl
  simp only [sfTriple] at hls0 hlf0 hle0 hls1 hlf1 hle1 hls2 hlf2 hle2
  have hs0 : bindFP z s c0.label.1.2.2.1.s := by rw [hls0, hev.1]; exact I.hs
  have hf0 : bindFP z c c0.label.1.2.2.1.f := by rw [hlf0, hev.2.1]; exact hc
  have hs1 : bindFP z s c1.label.1.2.2.1.s := by rw [hls1, hev.2.2.1]; exact I.hs
  have hf1 : bindFP z d c1.label.1.2.2.1.f := by rw [hlf1, hev.2.2.2.1]; exact hd
  have hshape : FormulaShape .s2 (.cell (.atom 2) (.cell c d)) := ⟨c, d, rfl⟩
  have hin : KidInputs .s2 s (.cell (.atom 2) (.cell c d))
      ([J c0.size c0 s c, J c1.size c1 s d,
        J c2.size c2 (J c0.size c0 s c).label.evaluation
          (J c1.size c1 s d).label.evaluation].map NTree.label) := by
    simp [KidInputs, J_subject, J_formula, hd_cell, tl_cell]
  have hcall0 : HonestCall G s c := by
    have h := honestCall_kid I.call hshape hin 0 (J c0.size c0 s c)
      (by simp [evalOrder, airNeedsSwap]) (fun j _ hj _ => absurd hj (by omega))
    rwa [J_subject, J_formula] at h
  have I0 : Inp (sv := sv) (ax := ax) z q G t S0 F0 c0 s c :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp), hcall0, ⟨n, e0, he0⟩,
      I.bs, I.bf.2.1, hs0, hf0⟩
  have G0 := IH0 _ _ I0
  have gen0 := kid_genuine G0 he0
  have hcall1 : HonestCall G s d := by
    have h := honestCall_kid I.call hshape hin 1 (J c1.size c1 s d)
      (by simp [evalOrder, airNeedsSwap])
      (by
        intro j k' hj hk'
        rcases j with _ | j
        · simp [evalOrder, airNeedsSwap] at hk'; subst hk'; exact gen0
        · omega)
    rwa [J_subject, J_formula] at h
  have I1 : Inp (sv := sv) (ax := ax) z q G t S0 F0 c1 s d :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp), hcall1, ⟨n, e1, he1⟩,
      I.bs, I.bf.2.2, hs1, hf1⟩
  have G1 := IH1 _ _ I1
  have gen1 := kid_genuine G1 he1
  have hev0 : (J c0.size c0 s c).label.evaluation = e0 := kid_eval G0 he0 le_rfl
  have hev1 : (J c1.size c1 s d).label.evaluation = e1 := kid_eval G1 he1 le_rfl
  have hcall2 : HonestCall G (J c0.size c0 s c).label.evaluation
      (J c1.size c1 s d).label.evaluation := by
    have h := honestCall_kid I.call hshape hin 2
      (J c2.size c2 (J c0.size c0 s c).label.evaluation (J c1.size c1 s d).label.evaluation)
      (by simp [evalOrder, airNeedsSwap])
      (by
        intro j k' hj hk'
        rcases j with _ | _ | j
        · simp [evalOrder, airNeedsSwap] at hk'; subst hk'; exact gen0
        · simp [evalOrder, airNeedsSwap] at hk'; subst hk'; exact gen1
        · omega)
    rwa [J_subject, J_formula] at h
  have he0b := kid_e_bind C.hz G0 hs0
  have he1b := kid_e_bind C.hz G1 hs1
  have hs2 : bindFP z (J c0.size c0 s c).label.evaluation c2.label.1.2.2.1.s := by
    rw [hls2, hev.2.2.2.2.1, ← hle0]; exact he0b
  have hf2 : bindFP z (J c1.size c1 s d).label.evaluation c2.label.1.2.2.1.f := by
    rw [hlf2, hev.2.2.2.2.2.1, ← hle1]; exact he1b
  have I2 : Inp (sv := sv) (ax := ax) z q G t S0 F0 c2 (J c0.size c0 s c).label.evaluation
      (J c1.size c1 s d).label.evaluation :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp), hcall2,
      ⟨n, r, by rw [hev0, hev1]; exact hr⟩,
      kid_eval_bounded C G0 he0 I.bs I.bf.2.1, kid_eval_bounded C G1 he1 I.bs I.bf.2.2, hs2, hf2⟩
  have G2 := IH2 _ _ I2
  exact ⟨C2ChipReady.op2 hst R.zRow hpubSt ha hc hd R.vcomp hle0 hle1 hle2 hls0 hls1 hls2
      G0.1 G1.1 G2.1,
    C2Aligned.op2 hst G0.2 G1.2 G2.2⟩

/-- **OP7.** -/
theorem step_s7 (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : Inp (sv := sv) (ax := ax) z q G t S0 F0 (.node row [c0, c1]) s f) (hst : row.1.1 = .s7)
    (IH0 : ∀ s' f', Inp (sv := sv) (ax := ax) z q G t S0 F0 c0 s' f' →
      Good (sv := sv) (ax := ax) z q c0 s' f')
    (IH1 : ∀ s' f', Inp (sv := sv) (ax := ax) z q G t S0 F0 c1 s' f' →
      Good (sv := sv) (ax := ax) z q c1 s' f') :
    Good (sv := sv) (ax := ax) z q (.node row [c0, c1]) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0 C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row [c0, c1]).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atom C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s7 := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  have hmb : memBlk row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.1
  simp only [memBlk, hpubSt] at hmb
  obtain ⟨fuel, r, hr⟩ := I.run
  cases fuel with
  | zero => simp [evalGBy] at hr
  | succ n =>
  obtain ⟨c, d, rfl⟩ : ∃ c d, b = .cell c d := by
    cases b with
    | atom _ => simp [evalGBy] at hr
    | cell c d => exact ⟨c, d, rfl⟩
  simp only [evalGBy] at hr
  obtain ⟨e1, he1⟩ : ∃ e1, evalGBy q n s c = some e1 := by
    cases h : evalGBy q n s c with
    | none => rw [h] at hr; simp at hr
    | some e1 => exact ⟨e1, rfl⟩
  rw [he1] at hr
  obtain ⟨m, hsz, hm⟩ := size_succ row [c0, c1]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hm1 : c1.size ≤ m := hm c1 (by simp)
  have hch : (J (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
      (.cell (.atom 7) (.cell c d))).children =
      [J c0.size c0 (J c1.size c1 s c).label.evaluation d, J c1.size c1 s c] := by
    rw [hsz, J_s7 (sv := sv) (ax := ax) _ _ row c0 c1 hst]
    simp only [NTree.children, nounHead, nounTail]
    rw [J_kid c1 _ _ hm1, J_kid c0 _ _ hm0]
  have hrec1 : c2Rec sv ax row.1.1 row.2 s (.cell (.atom 7) (.cell c d))
      ((J (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
        (.cell (.atom 7) (.cell c d))).children.map NTree.label) 1 = ⟨.cell c d, c, 2⟩ := by
    rw [hst, c2Rec_s7_1]; rfl
  obtain ⟨hc, hd⟩ := two_rec_prelude C I hb hrec1 (by rw [hst]; decide) ⟨_, hmb.1⟩ hmb.2.1
  obtain ⟨hls0, hlf0, hle0⟩ := link_at' C I.inT 0 (c := c0) rfl
  obtain ⟨hls1, hlf1, hle1⟩ := link_at' C I.inT 1 (c := c1) rfl
  simp only [sfTriple] at hls0 hlf0 hle0 hls1 hlf1 hle1
  have hs1 : bindFP z s c1.label.1.2.2.1.s := by rw [hls1, hev.2.2.2.1]; exact I.hs
  have hf1 : bindFP z c c1.label.1.2.2.1.f := by rw [hlf1, hev.2.2.2.2.1]; exact hc
  have hshape : FormulaShape .s7 (.cell (.atom 7) (.cell c d)) := ⟨c, d, rfl⟩
  have hin : KidInputs .s7 s (.cell (.atom 7) (.cell c d))
      ([J c0.size c0 (J c1.size c1 s c).label.evaluation d, J c1.size c1 s c].map NTree.label) := by
    simp [KidInputs, J_subject, J_formula, hd_cell, tl_cell]
  have hcall1 : HonestCall G s c := by
    have h := honestCall_kid I.call hshape hin 0 (J c1.size c1 s c)
      (by simp [evalOrder, airNeedsSwap, swapPair]) (fun j _ hj _ => absurd hj (by omega))
    rwa [J_subject, J_formula] at h
  have I1 : Inp (sv := sv) (ax := ax) z q G t S0 F0 c1 s c :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp), hcall1, ⟨n, e1, he1⟩,
      I.bs, I.bf.2.1, hs1, hf1⟩
  have G1 := IH1 _ _ I1
  have gen1 := kid_genuine G1 he1
  have hev1 : (J c1.size c1 s c).label.evaluation = e1 := kid_eval G1 he1 le_rfl
  have hcall0 : HonestCall G (J c1.size c1 s c).label.evaluation d := by
    have h := honestCall_kid I.call hshape hin 1 (J c0.size c0 (J c1.size c1 s c).label.evaluation d)
      (by simp [evalOrder, airNeedsSwap, swapPair])
      (by
        intro j k' hj hk'
        rcases j with _ | j
        · simp [evalOrder, airNeedsSwap, swapPair] at hk'; subst hk'; exact gen1
        · omega)
    rwa [J_subject, J_formula] at h
  have he1b := kid_e_bind C.hz G1 hs1
  have hs0 : bindFP z (J c1.size c1 s c).label.evaluation c0.label.1.2.2.1.s := by
    rw [hls0, hev.1, ← hle1]; exact he1b
  have hf0 : bindFP z d c0.label.1.2.2.1.f := by rw [hlf0, hev.2.1]; exact hd
  have I0 : Inp (sv := sv) (ax := ax) z q G t S0 F0 c0 (J c1.size c1 s c).label.evaluation d :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp), hcall0,
      ⟨n, r, by rw [hev1]; exact hr⟩,
      kid_eval_bounded C G1 he1 I.bs I.bf.2.1, I.bf.2.2, hs0, hf0⟩
  have G0 := IH0 _ _ I0
  exact ⟨C2ChipReady.op7 hst R.zRow hpubSt ha hc hd R.vcomp hle1 hle0 hls1 hls0 G1.1 G0.1,
    C2Aligned.op7 hst G1.2 G0.2⟩

/-- **OP8.** -/
theorem step_s8 (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : Inp (sv := sv) (ax := ax) z q G t S0 F0 (.node row [c0, c1]) s f) (hst : row.1.1 = .s8)
    (IH0 : ∀ s' f', Inp (sv := sv) (ax := ax) z q G t S0 F0 c0 s' f' →
      Good (sv := sv) (ax := ax) z q c0 s' f')
    (IH1 : ∀ s' f', Inp (sv := sv) (ax := ax) z q G t S0 F0 c1 s' f' →
      Good (sv := sv) (ax := ax) z q c1 s' f') :
    Good (sv := sv) (ax := ax) z q (.node row [c0, c1]) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0 C I
  have R := C.row _ I.inT
  have hcons : (NTree.node row [c0, c1]).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atom C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s8 := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  have hmb : memBlk row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.1
  simp only [memBlk, hpubSt] at hmb
  obtain ⟨fuel, r, hr⟩ := I.run
  cases fuel with
  | zero => simp [evalGBy] at hr
  | succ n =>
  obtain ⟨c, d, rfl⟩ : ∃ c d, b = .cell c d := by
    cases b with
    | atom _ => simp [evalGBy] at hr
    | cell c d => exact ⟨c, d, rfl⟩
  simp only [evalGBy] at hr
  obtain ⟨e1, he1⟩ : ∃ e1, evalGBy q n s c = some e1 := by
    cases h : evalGBy q n s c with
    | none => rw [h] at hr; simp at hr
    | some e1 => exact ⟨e1, rfl⟩
  rw [he1] at hr
  obtain ⟨m, hsz, hm⟩ := size_succ row [c0, c1]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hm1 : c1.size ≤ m := hm c1 (by simp)
  have hch : (J (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
      (.cell (.atom 8) (.cell c d))).children =
      [J c0.size c0 (.cell (J c1.size c1 s c).label.evaluation s) d, J c1.size c1 s c] := by
    rw [hsz, J_s8 (sv := sv) (ax := ax) _ _ row c0 c1 hst]
    simp only [NTree.children, nounHead, nounTail]
    rw [J_kid c1 _ _ hm1, J_kid c0 _ _ hm0]
  have hrec1 : c2Rec sv ax row.1.1 row.2 s (.cell (.atom 8) (.cell c d))
      ((J (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
        (.cell (.atom 8) (.cell c d))).children.map NTree.label) 1 = ⟨.cell c d, c, 2⟩ := by
    rw [hst, c2Rec_s8_1]; rfl
  obtain ⟨hc, hd⟩ := two_rec_prelude C I hb hrec1 (by rw [hst]; decide) ⟨_, hmb.1⟩ hmb.2.1
  obtain ⟨hls0, hlf0, hle0⟩ := link_at' C I.inT 0 (c := c0) rfl
  obtain ⟨hls1, hlf1, hle1⟩ := link_at' C I.inT 1 (c := c1) rfl
  simp only [sfTriple] at hls0 hlf0 hle0 hls1 hlf1 hle1
  have hs1 : bindFP z s c1.label.1.2.2.1.s := by rw [hls1, hev.2.2.2.1]; exact I.hs
  have hf1 : bindFP z c c1.label.1.2.2.1.f := by rw [hlf1, hev.2.2.2.2.1]; exact hc
  have hshape : FormulaShape .s8 (.cell (.atom 8) (.cell c d)) := ⟨c, d, rfl⟩
  have hin : KidInputs .s8 s (.cell (.atom 8) (.cell c d))
      ([J c0.size c0 (.cell (J c1.size c1 s c).label.evaluation s) d, J c1.size c1 s c].map
        NTree.label) := by
    simp [KidInputs, J_subject, J_formula, hd_cell, tl_cell]
  have hcall1 : HonestCall G s c := by
    have h := honestCall_kid I.call hshape hin 0 (J c1.size c1 s c)
      (by simp [evalOrder, airNeedsSwap, swapPair]) (fun j _ hj _ => absurd hj (by omega))
    rwa [J_subject, J_formula] at h
  have I1 : Inp (sv := sv) (ax := ax) z q G t S0 F0 c1 s c :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp), hcall1, ⟨n, e1, he1⟩,
      I.bs, I.bf.2.1, hs1, hf1⟩
  have G1 := IH1 _ _ I1
  have gen1 := kid_genuine G1 he1
  have hev1 : (J c1.size c1 s c).label.evaluation = e1 := kid_eval G1 he1 le_rfl
  have hcall0 : HonestCall G (.cell (J c1.size c1 s c).label.evaluation s) d := by
    have h := honestCall_kid I.call hshape hin 1
      (J c0.size c0 (.cell (J c1.size c1 s c).label.evaluation s) d)
      (by simp [evalOrder, airNeedsSwap, swapPair])
      (by
        intro j k' hj hk'
        rcases j with _ | j
        · simp [evalOrder, airNeedsSwap, swapPair] at hk'; subst hk'; exact gen1
        · omega)
    rwa [J_subject, J_formula] at h
  have he1b := kid_e_bind C.hz G1 hs1
  have hs0 : bindFP z (.cell (J c1.size c1 s c).label.evaluation s) c0.label.1.2.2.1.s := by
    have hz' : row.1.2.1.z = z := R.zRow
    rw [hls0, hev.1, hz']
    exact Batch525.bindFP_cons C.hz _ _ _ _ (hle1 ▸ he1b) I.hs
  have hf0 : bindFP z d c0.label.1.2.2.1.f := by rw [hlf0, hev.2.1]; exact hd
  have I0 : Inp (sv := sv) (ax := ax) z q G t S0 F0 c0
      (.cell (J c1.size c1 s c).label.evaluation s) d :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp), hcall0,
      ⟨n, r, by rw [hev1]; exact hr⟩,
      ⟨kid_eval_bounded C G1 he1 I.bs I.bf.2.1, I.bs⟩, I.bf.2.2, hs0, hf0⟩
  have G0 := IH0 _ _ I0
  exact ⟨C2ChipReady.op8 hst R.zRow hpubSt ha hc hd R.vcomp hle1 hle0 hls1 hls0 G1.1 G0.1,
    C2Aligned.op8 hst G1.2 G0.2⟩

end Internal2

/-! ## §H  OP6 and OP9, and the induction -/

section Internal3

variable {z : K} {q Λ : ℕ} {G : NTree (GenComputeRow K)}
  {t : NTree ((State × DTcomp K) × ℕ)} {S0 F0 : Noun}

theorem c6b_eq_condBit (n : Noun) : Batch1091.c6b n = condBit n := by cases n <;> rfl

/-- **OP6.** -/
theorem step_s6 (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : Inp (sv := sv) (ax := ax) z q G t S0 F0 (.node row [c0, c1]) s f) (hst : row.1.1 = .s6)
    (IH0 : ∀ s' f', Inp (sv := sv) (ax := ax) z q G t S0 F0 c0 s' f' →
      Good (sv := sv) (ax := ax) z q c0 s' f')
    (IH1 : ∀ s' f', Inp (sv := sv) (ax := ax) z q G t S0 F0 c1 s' f' →
      Good (sv := sv) (ax := ax) z q c1 s' f') :
    Good (sv := sv) (ax := ax) z q (.node row [c0, c1]) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0 C I
  have R := C.row _ I.inT
  have hz' : row.1.2.1.z = z := R.zRow
  have hcons : (NTree.node row [c0, c1]).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atom C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s6 := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  have hmb : memBlk row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.1
  simp only [memBlk, hpubSt] at hmb
  obtain ⟨fuel, r, hr⟩ := I.run
  cases fuel with
  | zero => simp [evalGBy] at hr
  | succ n =>
  obtain ⟨c, d, e, rfl⟩ : ∃ c d e, b = .cell c (.cell d e) := by
    cases b with
    | atom _ => simp [evalGBy] at hr
    | cell c b2 =>
      cases b2 with
      | atom _ => simp [evalGBy] at hr
      | cell d e => exact ⟨c, d, e, rfl⟩
  simp only [evalGBy] at hr
  obtain ⟨bb, hb01, hcond, hrT⟩ : ∃ bb, (bb = 0 ∨ bb = 1) ∧ evalGBy q n s c = some (.atom bb) ∧
      evalGBy q n s (if bb = 0 then d else e) = some r := by
    cases h : evalGBy q n s c with
    | none => rw [h] at hr; simp at hr
    | some v =>
      rw [h] at hr
      cases v with
      | cell _ _ => simp at hr
      | atom k =>
        rcases k with _ | _ | k
        · exact ⟨0, Or.inl rfl, rfl, by simpa using hr⟩
        · exact ⟨1, Or.inr rfl, rfl, by simpa using hr⟩
        · simp at hr
  obtain ⟨m, hsz, hm⟩ := size_succ row [c0, c1]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hm1 : c1.size ≤ m := hm c1 (by simp)
  have hch : (J (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
      (.cell (.atom 6) (.cell c (.cell d e)))).children =
      [J c0.size c0 s (if Batch1091.c6b (J c1.size c1 s c).label.evaluation = 0 then d else e),
        J c1.size c1 s c] := by
    rw [hsz, J_s6 (sv := sv) (ax := ax) _ _ row c0 c1 hst]
    simp only [NTree.children, nounHead, nounTail]
    simp only [J_kid c1 s c hm1, J_kid c0 s _ hm0]
    try rfl
  have hrec1 : c2Rec sv ax row.1.1 row.2 s (.cell (.atom 6) (.cell c (.cell d e)))
      ((J (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
        (.cell (.atom 6) (.cell c (.cell d e)))).children.map NTree.label) 1 =
      ⟨.cell c (.cell d e), c, 2⟩ := by
    rw [hst, c2Rec_s6_1]; rfl
  have hrec2 : c2Rec sv ax row.1.1 row.2 s (.cell (.atom 6) (.cell c (.cell d e)))
      ((J (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
        (.cell (.atom 6) (.cell c (.cell d e)))).children.map NTree.label) 2 =
      ⟨.cell d e, d, 2⟩ := by
    rw [hst, c2Rec_s6_2]; rfl
  have hcons1 : FP.cons z row.1.2.2.2.f_th row.1.2.2.2.f_tt = row.1.2.2.2.f_t := by
    rw [← hz']; exact hmb.2.1
  have hcons2 : FP.cons z row.1.2.2.2.f_tth row.1.2.2.2.f_ttt = row.1.2.2.2.f_tt := by
    rw [← hz']; exact hmb.2.2.2.1
  obtain ⟨hc, hde⟩ := tail_bind2 C I hb
    (by show (1 : ℕ) < Nock.Framework.recordCount row.1.1; rw [hst]; decide) hrec1 ⟨_, hmb.1⟩ hcons1
  obtain ⟨hd, he⟩ := tail_bind3 C I hde
    (by show (2 : ℕ) < Nock.Framework.recordCount row.1.1; rw [hst]; decide) hrec2 ⟨_, hmb.2.2.1⟩
    hcons2
  obtain ⟨hls0, hlf0, hle0⟩ := link_at' C I.inT 0 (c := c0) rfl
  obtain ⟨hls1, hlf1, hle1⟩ := link_at' C I.inT 1 (c := c1) rfl
  simp only [sfTriple] at hls0 hlf0 hle0 hls1 hlf1 hle1
  have hs1 : bindFP z s c1.label.1.2.2.1.s := by rw [hls1, hev.2.2.2.1]; exact I.hs
  have hf1 : bindFP z c c1.label.1.2.2.1.f := by rw [hlf1, hev.2.2.2.2.1]; exact hc
  have hshape : FormulaShape .s6 (.cell (.atom 6) (.cell c (.cell d e))) := ⟨c, d, e, rfl⟩
  have hin : KidInputs .s6 s (.cell (.atom 6) (.cell c (.cell d e)))
      ([J c0.size c0 s (if Batch1091.c6b (J c1.size c1 s c).label.evaluation = 0 then d else e),
        J c1.size c1 s c].map NTree.label) := by
    simp [KidInputs, J_subject, J_formula, hd_cell, tl_cell, c6b_eq_condBit]
  have hcall1 : HonestCall G s c := by
    have h := honestCall_kid I.call hshape hin 0 (J c1.size c1 s c)
      (by simp [evalOrder, airNeedsSwap, swapPair]) (fun j _ hj _ => absurd hj (by omega))
    rwa [J_subject, J_formula] at h
  have I1 : Inp (sv := sv) (ax := ax) z q G t S0 F0 c1 s c :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp), hcall1,
      ⟨n, _, hcond⟩, I.bs, I.bf.2.1, hs1, hf1⟩
  have G1 := IH1 _ _ I1
  have gen1 := kid_genuine G1 hcond
  have hev1 : (J c1.size c1 s c).label.evaluation = .atom bb := kid_eval G1 hcond le_rfl
  have hb' : Batch1091.c6b (J c1.size c1 s c).label.evaluation = bb := by rw [hev1]; rfl
  have hcall0 : HonestCall G s (if bb = 0 then d else e) := by
    have h := honestCall_kid I.call hshape hin 1
      (J c0.size c0 s (if Batch1091.c6b (J c1.size c1 s c).label.evaluation = 0 then d else e))
      (by simp [evalOrder, airNeedsSwap, swapPair])
      (by
        intro j k' hj hk'
        rcases j with _ | j
        · simp [evalOrder, airNeedsSwap, swapPair] at hk'; subst hk'; exact gen1
        · omega)
    rw [J_subject, J_formula, hb'] at h
    exact h
  rw [hb'] at hch
  have he1b := kid_e_bind C.hz G1 hs1
  rw [hev1] at he1b
  have hleaf : row.1.2.2.1.sf2_e.leaf = (bb : K) := by
    rw [← hle1]; exact atomFP_leaf_eq he1b
  have hf0 : bindFP z (if bb = 0 then d else e) c0.label.1.2.2.1.f := by
    rw [hlf0, hev.2.1, hleaf]
    rcases hb01 with rfl | rfl
    · simpa using hd
    · simpa using he
  have hs0 : bindFP z s c0.label.1.2.2.1.s := by rw [hls0, hev.1]; exact I.hs
  have bf0 : BoundedBy q (if bb = 0 then d else e) := by
    rcases hb01 with rfl | rfl
    · simpa using I.bf.2.2.1
    · simpa using I.bf.2.2.2
  have I0 : Inp (sv := sv) (ax := ax) z q G t S0 F0 c0 s (if bb = 0 then d else e) :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp), hcall0,
      ⟨n, r, hrT⟩, I.bs, bf0, hs0, hf0⟩
  have G0 := IH0 _ _ I0
  refine ⟨C2ChipReady.op6 hst R.zRow hpubSt ha hc hd he hb01 hev1 R.vcomp hle0 hle1 hls0 hls1
      G0.1 G1.1, C2Aligned.op6 hst G1.2 ?_⟩
  rw [hb']; exact G0.2

/-- The core of an OP9 row is an honest call (the generator runs it first, no sibling needed). -/
theorem honestCall_s9_core {G : NTree (GenComputeRow K)} {subj c : Noun} {a : ℕ}
    (hcall : HonestCall G subj (.cell (.atom 9) (.cell (.atom a) c))) : HonestCall G subj c := by
  obtain ⟨n, sub, r, hgen, hG⟩ := hcall
  cases n with
  | zero => simp [genComputeSkeleton] at hgen
  | succ n =>
  cases hc : genComputeSkeleton (K := K) n subj c with
  | error e => simp [genComputeSkeleton, hc] at hgen
  | ok p =>
    obtain ⟨tC, core⟩ := p
    cases hsl : Noun.slot a core with
    | none => simp [genComputeSkeleton, hc, hsl] at hgen
    | some arm =>
    cases hi : genComputeSkeleton (K := K) n core arm with
    | error e => simp [genComputeSkeleton, hc, hsl, hi] at hgen
    | ok q =>
      obtain ⟨tI, rI⟩ := q
      simp [genComputeSkeleton, hc, hsl, hi] at hgen
      obtain ⟨rfl, rfl⟩ := hgen
      exact honestCall_of_child hG hc
        (by simp [airReorder_node, airNeedsSwap, skelNode, genSkelOp9, NTree.children])

/-- **OP9.** -/
theorem step_s9 (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)} {s f : Noun}
    (I : Inp (sv := sv) (ax := ax) z q G t S0 F0 (.node row [c0, c1]) s f) (hst : row.1.1 = .s9)
    (IH0 : ∀ s' f', Inp (sv := sv) (ax := ax) z q G t S0 F0 c0 s' f' →
      Good (sv := sv) (ax := ax) z q c0 s' f')
    (IH1 : ∀ s' f', Inp (sv := sv) (ax := ax) z q G t S0 F0 c1 s' f' →
      Good (sv := sv) (ax := ax) z q c1 s' f') :
    Good (sv := sv) (ax := ax) z q (.node row [c0, c1]) s f := by
  obtain ⟨a, b, rfl, hb, ha⟩ := slot0 C I
  have R := C.row _ I.inT
  have hz' : row.1.2.1.z = z := R.zRow
  have hcons : (NTree.node row [c0, c1]).label.1.1 ≠ .cons := by simp [hst]
  have ha' := head_atom C I hcons ha
  simp only [NTree.label, hst, State.toNat] at ha'
  subst ha'
  have hpubSt : row.1.2.2.1.state = .s9 := R.pubSt.trans hst
  have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.2
  simp only [evalV, hpubSt] at hev
  have hmb : memBlk row.1.2.1 row.1.2.2.1 row.1.2.2.2 := R.vcomp.2.2.2.1
  simp only [memBlk, hpubSt] at hmb
  obtain ⟨fuel, r, hr⟩ := I.run
  cases fuel with
  | zero => simp [evalGBy] at hr
  | succ n =>
  obtain ⟨ax', c, rfl⟩ : ∃ ax' c, b = .cell (.atom ax') c := by
    cases b with
    | atom _ => simp [evalGBy] at hr
    | cell b1 c =>
      cases b1 with
      | cell _ _ => simp [evalGBy] at hr
      | atom ax' => exact ⟨ax', c, rfl⟩
  simp only [evalGBy] at hr
  obtain ⟨core, hcore⟩ : ∃ core, evalGBy q n s c = some core := by
    cases h : evalGBy q n s c with
    | none => rw [h] at hr; simp at hr
    | some core => exact ⟨core, rfl⟩
  rw [hcore] at hr
  dsimp only at hr
  obtain ⟨arm, hslot⟩ : ∃ arm, Noun.slot ax' core = some arm := by
    cases h : Noun.slot ax' core with
    | none => rw [h] at hr; simp at hr
    | some arm => exact ⟨arm, rfl⟩
  rw [hslot] at hr
  dsimp only at hr
  -- the certificate axis is the formula's
  have hrec1 : c2Rec sv ax row.1.1 row.2 s (.cell (.atom 9) (.cell (.atom ax') c))
      ((J (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
        (.cell (.atom 9) (.cell (.atom ax') c))).children.map NTree.label) 1 =
      ⟨.cell (.atom ax') c, .atom ax', 2⟩ := by
    rw [hst, c2Rec_s9_1]; rfl
  have hcons1 : FP.cons z row.1.2.2.2.f_th row.1.2.2.2.f_tt = row.1.2.2.2.f_t := by
    rw [← hz']; exact hmb.2.1
  obtain ⟨hth, hc⟩ := tail_bind2 C I hb
    (by show (1 : ℕ) < Nock.Framework.recordCount row.1.1; rw [hst]; decide) hrec1 ⟨_, hmb.1⟩ hcons1
  have hax := R.ax9 hst
  have hleaf : row.1.2.2.2.f_th.leaf = (ax' : K) := atomFP_leaf_eq hth
  have haxeq : ax (row.2 + 3) = ax' :=
    natCast_inj_of_lt' C hax.2 (by simpa using I.bf.2.1) (by rw [← hleaf]; exact hax.1)
  subst haxeq
  obtain ⟨m, hsz, hm⟩ := size_succ row [c0, c1]
  have hm0 : c0.size ≤ m := hm c0 (by simp)
  have hm1 : c1.size ≤ m := hm c1 (by simp)
  have hch : (J (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
      (.cell (.atom 9) (.cell (.atom (ax (row.2 + 3))) c))).children =
      [J c0.size c0 s c,
        J c1.size c1 (J c0.size c0 s c).label.evaluation (sv .verify_child (row.2 + 3))] := by
    rw [hsz, J_s9 (sv := sv) (ax := ax) _ _ row c0 c1 hst]
    simp only [NTree.children, nounHead, nounTail]
    rw [J_kid c0 _ _ hm0, J_kid c1 _ _ hm1]
  obtain ⟨hls0, hlf0, hle0⟩ := link_at' C I.inT 0 (c := c0) rfl
  obtain ⟨hls1, hlf1, hle1⟩ := link_at' C I.inT 1 (c := c1) rfl
  simp only [sfTriple] at hls0 hlf0 hle0 hls1 hlf1 hle1
  have hs0 : bindFP z s c0.label.1.2.2.1.s := by rw [hls0, hev.1]; exact I.hs
  have hf0 : bindFP z c c0.label.1.2.2.1.f := by rw [hlf0, hev.2.1]; exact hc
  have hcall0 : HonestCall G s c := honestCall_s9_core I.call
  have I0 : Inp (sv := sv) (ax := ax) z q G t S0 F0 c0 s c :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp), hcall0,
      ⟨n, core, hcore⟩, I.bs, I.bf.2.2, hs0, hf0⟩
  have G0 := IH0 _ _ I0
  have gen0 := kid_genuine G0 hcore
  have hev0 : (J c0.size c0 s c).label.evaluation = core := kid_eval G0 hcore le_rfl
  have he0b := kid_e_bind C.hz G0 hs0
  -- record 2: the served arm is the slot of the core
  have hrec := C.recs _ s _ I.inT I.reach
  have hj2 : ((2 : Fin 3) : ℕ) < Nock.Framework.recordCount
      (J (NTree.node row [c0, c1]).size (.node row [c0, c1]) s
        (.cell (.atom 9) (.cell (.atom (ax (row.2 + 3))) c))).label.state := by
    rw [J_label_eq]; simp [hst, Nock.Framework.recordCount]
  have h2 := hrec 2 hj2
  rw [J_rec] at h2
  simp only [NTree.label, Fin.val_two] at h2
  rw [hst, c2Rec_s9_2, hch] at h2
  simp only [kidSkel, List.map_cons, List.map_nil, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, J_formula] at h2
  have hmr : traceRec row 2 = row.1.2.2.1.mr3 := rfl
  rw [hmr, hmb.2.2.1] at h2
  obtain ⟨hslot', harm⟩ := h2 (by rw [← hle0]; exact enc_eq_of_bind he0b)
    (kid_eval_le C G0 hcall0 hcore) (kid_eval_bounded C G0 hcore I.bs I.bf.2.2)
  have harm_eq : sv .verify_child (row.2 + 3) = arm := by
    rw [hev0, hslot] at hslot'; exact (Option.some.inj hslot').symm
  have hshape : FormulaShape .s9 (.cell (.atom 9) (.cell (.atom (ax (row.2 + 3))) c)) :=
    ⟨ax (row.2 + 3), c, rfl⟩
  have hin : KidInputs .s9 s (.cell (.atom 9) (.cell (.atom (ax (row.2 + 3))) c))
      ([J c0.size c0 s c,
        J c1.size c1 (J c0.size c0 s c).label.evaluation (sv .verify_child (row.2 + 3))].map
          NTree.label) := by
    simp [KidInputs, J_subject, J_formula, tl_cell, op9Axis, hslot']
  have hcall1 : HonestCall G (J c0.size c0 s c).label.evaluation (sv .verify_child (row.2 + 3)) := by
    have h := honestCall_kid I.call hshape hin 1
      (J c1.size c1 (J c0.size c0 s c).label.evaluation (sv .verify_child (row.2 + 3)))
      (by simp [evalOrder, airNeedsSwap])
      (by
        intro j k' hj hk'
        rcases j with _ | j
        · simp [evalOrder, airNeedsSwap] at hk'; subst hk'; exact gen0
        · omega)
    rwa [J_subject, J_formula] at h
  have hs1 : bindFP z (J c0.size c0 s c).label.evaluation c1.label.1.2.2.1.s := by
    rw [hls1, hev.2.2.1, ← hle0]; exact he0b
  have hf1 : bindFP z (sv .verify_child (row.2 + 3)) c1.label.1.2.2.1.f := by
    rw [hlf1]; exact harm.symm
  have I1 : Inp (sv := sv) (ax := ax) z q G t S0 F0 c1 (J c0.size c0 s c).label.evaluation
      (sv .verify_child (row.2 + 3)) :=
    ⟨inT_child I.inT (by simp), reach_child I.reach (by rw [hch]; simp), hcall1,
      ⟨n, r, by rw [hev0, harm_eq]; exact hr⟩,
      kid_eval_bounded C G0 hcore I.bs I.bf.2.2,
      slot_boundedBy q _ _ (kid_eval_bounded C G0 hcore I.bs I.bf.2.2) hslot', hs1, hf1⟩
  have G1 := IH1 _ _ I1
  exact ⟨C2ChipReady.op9 hst R.zRow hpubSt ha hth hc harm.symm hax.1 R.vcomp hle0 hle1 hls0 hls1
      G0.1 G1.1,
    C2Aligned.op9 hst G0.2 hslot' G1.2⟩

/-- **The combined evaluation-order induction.**  Every node reached by the C2 join of the root,
at an honest call with a guarded run and bound inputs, is chip-ready and aligned. -/
theorem good_of_inp (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0) :
    ∀ (n : ℕ) (u : NTree ((State × DTcomp K) × ℕ)) (s f : Noun), u.size ≤ n →
      Inp (sv := sv) (ax := ax) z q G t S0 F0 u s f → Good (sv := sv) (ax := ax) z q u s f := by
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
    have IHc : ∀ c ∈ ch, ∀ s' f', Inp (sv := sv) (ax := ax) z q G t S0 F0 c s' f' →
        Good (sv := sv) (ax := ax) z q c s' f' := fun c hc s' f' I' =>
      ih c s' f' (Batch1021.child_size_le_of_node hu hc) I'
    cases hst : row.1.1 with
    | s0 =>
        rcases ch with _ | ⟨c0, rest⟩
        · exact step_s0 C I hst
        · rw [hst] at har; simp [fanoutComp] at har
    | s1 =>
        rcases ch with _ | ⟨c0, rest⟩
        · exact step_s1 C I hst
        · rw [hst] at har; simp [fanoutComp] at har
    | s2 =>
        rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, rest⟩⟩⟩⟩ <;>
          try (rw [hst] at har; simp [fanoutComp] at har; done)
        exact step_s2 C I hst (IHc c0 (by simp)) (IHc c1 (by simp)) (IHc c2 (by simp))
    | s3 =>
        rcases ch with _ | ⟨c0, _ | ⟨c1, rest⟩⟩ <;>
          try (rw [hst] at har; simp [fanoutComp] at har; done)
        exact step_s3 C I hst (IHc c0 (by simp))
    | s4 =>
        rcases ch with _ | ⟨c0, _ | ⟨c1, rest⟩⟩ <;>
          try (rw [hst] at har; simp [fanoutComp] at har; done)
        exact step_s4 C I hst (IHc c0 (by simp))
    | s5 =>
        rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩ <;>
          try (rw [hst] at har; simp [fanoutComp] at har; done)
        exact step_s5 C I hst (IHc c0 (by simp)) (IHc c1 (by simp))
    | s6 =>
        rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩ <;>
          try (rw [hst] at har; simp [fanoutComp] at har; done)
        exact step_s6 C I hst (IHc c0 (by simp)) (IHc c1 (by simp))
    | s7 =>
        rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩ <;>
          try (rw [hst] at har; simp [fanoutComp] at har; done)
        exact step_s7 C I hst (IHc c0 (by simp)) (IHc c1 (by simp))
    | s8 =>
        rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩ <;>
          try (rw [hst] at har; simp [fanoutComp] at har; done)
        exact step_s8 C I hst (IHc c0 (by simp)) (IHc c1 (by simp))
    | s9 =>
        rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩ <;>
          try (rw [hst] at har; simp [fanoutComp] at har; done)
        exact step_s9 C I hst (IHc c0 (by simp)) (IHc c1 (by simp))
    | cons =>
        rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩ <;>
          try (rw [hst] at har; simp [fanoutComp] at har; done)
        exact step_cons C I hst (IHc c0 (by simp)) (IHc c1 (by simp))

/-- **The root.**  `C2ChipReady` and `C2Aligned` at the root inputs `(S0, F0)` from the context,
the root's honest call (the generator run of the claim), a guarded run, bounded root inputs, and
the root subject / formula bindings. -/
theorem root_good (C : Ctx (sv := sv) (ax := ax) z q Λ G t S0 F0)
    (hcall : HonestCall G S0 F0) (hrun : ∃ fuel r, evalGBy q fuel S0 F0 = some r)
    (bs : BoundedBy q S0) (bf : BoundedBy q F0)
    (hs : bindFP z S0 t.label.1.2.2.1.s) (hf : bindFP z F0 t.label.1.2.2.1.f) :
    C2ChipReady (sv := sv) (ax := ax) z q t S0 F0 ∧ C2Aligned (sv := sv) (ax := ax) t S0 F0 :=
  good_of_inp C t.size t S0 F0 le_rfl ⟨InTree.here _, InTree.here _, hcall, hrun, bs, bf, hs, hf⟩

end Internal3



section Step1

/-! ### (1) KidInputs of the join's children, built order -/

theorem kidInputs_op2 (n : ℕ) (row : (State × DTcomp K) × ℕ)
    (c0 c1 c2 : NTree ((State × DTcomp K) × ℕ)) (subj b c : Noun) (h : row.1.1 = .s2) :
    KidInputs .s2 subj (.cell (.atom 2) (.cell b c))
      ((J (n + 1) (.node row [c0, c1, c2]) subj (.cell (.atom 2) (.cell b c))).children.map
        NTree.label) := by
  rw [J_s2 (sv := sv) (ax := ax) _ _ row c0 c1 c2 h]
  simp [KidInputs, NTree.children, J_subject, J_formula, nounHead, nounTail, hd_cell, tl_cell]

theorem kidInputs_op9 (n : ℕ) (row : (State × DTcomp K) × ℕ)
    (c0 c1 : NTree ((State × DTcomp K) × ℕ)) (subj fc : Noun) (a : ℕ) (h : row.1.1 = .s9)
    (hslot : Noun.slot a (J n c0 subj fc).label.evaluation =
      some (sv .verify_child (row.2 + 3))) :
    KidInputs .s9 subj (.cell (.atom 9) (.cell (.atom a) fc))
      ((J (n + 1) (.node row [c0, c1]) subj (.cell (.atom 9) (.cell (.atom a) fc))).children.map
        NTree.label) := by
  rw [J_s9 (sv := sv) (ax := ax) _ _ row c0 c1 h]
  simp [KidInputs, NTree.children, J_subject, J_formula, nounHead, nounTail, op9Axis, hslot, hd_cell, tl_cell]

theorem kidInputs_op7 (n : ℕ) (row : (State × DTcomp K) × ℕ)
    (c0 c1 : NTree ((State × DTcomp K) × ℕ)) (subj b c : Noun) (h : row.1.1 = .s7) :
    KidInputs .s7 subj (.cell (.atom 7) (.cell b c))
      ((J (n + 1) (.node row [c0, c1]) subj (.cell (.atom 7) (.cell b c))).children.map
        NTree.label) := by
  rw [J_s7 (sv := sv) (ax := ax) _ _ row c0 c1 h]
  simp [KidInputs, NTree.children, J_subject, J_formula, nounHead, nounTail, hd_cell, tl_cell]

theorem kidInputs_op6 (n : ℕ) (row : (State × DTcomp K) × ℕ)
    (c0 c1 : NTree ((State × DTcomp K) × ℕ)) (subj b c d : Noun) (h : row.1.1 = .s6) :
    KidInputs .s6 subj (.cell (.atom 6) (.cell b (.cell c d)))
      ((J (n + 1) (.node row [c0, c1]) subj (.cell (.atom 6) (.cell b (.cell c d)))).children.map
        NTree.label) := by
  rw [J_s6 (sv := sv) (ax := ax) _ _ row c0 c1 h]
  simp only [List.map_cons, List.map_nil, NTree.children, KidInputs]
  refine ⟨J_subject _ _ _ _, ?_, J_subject _ _ _ _, ?_⟩
  · rw [J_formula]; rfl
  · rw [J_formula]
    unfold condBit
    cases (J n c1 subj b).label.evaluation <;> rfl

/-! ### (2) evalOrder at the computed-formula rows -/

theorem evalOrder_s2 {α : Type*} (l : List α) : evalOrder .s2 l = l := by
  simp [evalOrder, airNeedsSwap]

theorem evalOrder_s9 {α : Type*} (l : List α) : evalOrder .s9 l = l := by
  simp [evalOrder, airNeedsSwap]

theorem evalOrder_s7 {α : Type*} (a b : α) : evalOrder .s7 [a, b] = [b, a] := by
  simp [evalOrder, airNeedsSwap, swapPair]



/-- **OP2's third child.**  Built child 2 (`sf3`), subject child 0's evaluation, formula child 1's
evaluation, is at an honest call of `G` as soon as children 0 and 1 are genuine; its inputs are
inside the window. -/
theorem honestCall_op2_third {G : NTree (GenComputeRow K)} (n : ℕ)
    (row : (State × DTcomp K) × ℕ) (c0 c1 c2 : NTree ((State × DTcomp K) × ℕ))
    (subj b c : Noun) (h : row.1.1 = .s2)
    (hcall : HonestCall G subj (.cell (.atom 2) (.cell b c)))
    (g0 : GenuineSkel (J n c0 subj b)) (g1 : GenuineSkel (J n c1 subj c)) :
    HonestCall G (J n c0 subj b).label.evaluation (J n c1 subj c).label.evaluation ∧
      (J n c0 subj b).label.evaluation.leaves ≤ programLeafBound (airReorder G) ∧
      (J n c1 subj c).label.evaluation.leaves ≤ programLeafBound (airReorder G) := by
  have hin := kidInputs_op2 (sv := sv) (ax := ax) n row c0 c1 c2 subj b c h
  have hshape : FormulaShape .s2 (.cell (.atom 2) (.cell b c)) := ⟨b, c, rfl⟩
  have hkids : (J (n + 1) (.node row [c0, c1, c2]) subj (.cell (.atom 2) (.cell b c))).children =
      [J n c0 subj b, J n c1 subj c,
        J n c2 (J n c0 subj b).label.evaluation (J n c1 subj c).label.evaluation] := by
    rw [J_s2 (sv := sv) (ax := ax) _ _ row c0 c1 c2 h]; rfl
  rw [hkids] at hin
  have hk := honestCall_kid hcall hshape hin 2
    (J n c2 (J n c0 subj b).label.evaluation (J n c1 subj c).label.evaluation)
    (by simp [evalOrder_s2])
    (by
      intro j k' hj hk'
      rw [evalOrder_s2] at hk'
      rcases j with _ | _ | j
      · simp at hk'; subst hk'; exact g0
      · simp at hk'; subst hk'; exact g1
      · omega)
  rw [J_subject, J_formula] at hk
  exact ⟨hk, (honestCall_inputs_le hk).1, (honestCall_inputs_le hk).2⟩

/-- **OP9's arm.**  Built child 1 (`sf2`), subject the core's evaluation, formula the SERVED noun
`sv .verify_child (S+3)`, is at an honest call as soon as the core is genuine and the served noun is
the noun-level slot of the core (`ServedLookup` + `axis_sound_recognizer'`, item (ii)). -/
theorem honestCall_op9_arm {G : NTree (GenComputeRow K)} (n : ℕ)
    (row : (State × DTcomp K) × ℕ) (c0 c1 : NTree ((State × DTcomp K) × ℕ))
    (subj fc : Noun) (a : ℕ) (h : row.1.1 = .s9)
    (hcall : HonestCall G subj (.cell (.atom 9) (.cell (.atom a) fc)))
    (hslot : Noun.slot a (J n c0 subj fc).label.evaluation =
      some (sv .verify_child (row.2 + 3)))
    (g0 : GenuineSkel (J n c0 subj fc)) :
    HonestCall G (J n c0 subj fc).label.evaluation (sv .verify_child (row.2 + 3)) ∧
      (J n c0 subj fc).label.evaluation.leaves ≤ programLeafBound (airReorder G) ∧
      (sv .verify_child (row.2 + 3)).leaves ≤ programLeafBound (airReorder G) := by
  have hin := kidInputs_op9 (sv := sv) (ax := ax) n row c0 c1 subj fc a h hslot
  have hshape : FormulaShape .s9 (.cell (.atom 9) (.cell (.atom a) fc)) := ⟨a, fc, rfl⟩
  have hkids : (J (n + 1) (.node row [c0, c1]) subj
      (.cell (.atom 9) (.cell (.atom a) fc))).children =
      [J n c0 subj fc, J n c1 (J n c0 subj fc).label.evaluation (sv .verify_child (row.2 + 3))] := by
    rw [J_s9 (sv := sv) (ax := ax) _ _ row c0 c1 h]; rfl
  rw [hkids] at hin
  have hk := honestCall_kid hcall hshape hin 1
    (J n c1 (J n c0 subj fc).label.evaluation (sv .verify_child (row.2 + 3)))
    (by simp [evalOrder_s9])
    (by
      intro j k' hj hk'
      rw [evalOrder_s9] at hk'
      rcases j with _ | j
      · simp at hk'; subst hk'; exact g0
      · omega)
  rw [J_subject, J_formula] at hk
  exact ⟨hk, (honestCall_inputs_le hk).1, (honestCall_inputs_le hk).2⟩

/-- **OP7, the swapped row (control).**  Built child 0 (`sf1`, the continuation) comes SECOND in
`evalOrder`; it is an honest call once built child 1 (`sf2`, the helper) is genuine. -/
theorem honestCall_op7_cons {G : NTree (GenComputeRow K)} (n : ℕ)
    (row : (State × DTcomp K) × ℕ) (c0 c1 : NTree ((State × DTcomp K) × ℕ))
    (subj b c : Noun) (h : row.1.1 = .s7)
    (hcall : HonestCall G subj (.cell (.atom 7) (.cell b c)))
    (g1 : GenuineSkel (J n c1 subj b)) :
    HonestCall G (J n c1 subj b).label.evaluation c := by
  have hin := kidInputs_op7 (sv := sv) (ax := ax) n row c0 c1 subj b c h
  have hshape : FormulaShape .s7 (.cell (.atom 7) (.cell b c)) := ⟨b, c, rfl⟩
  have hkids : (J (n + 1) (.node row [c0, c1]) subj (.cell (.atom 7) (.cell b c))).children =
      [J n c0 (J n c1 subj b).label.evaluation c, J n c1 subj b] := by
    rw [J_s7 (sv := sv) (ax := ax) _ _ row c0 c1 h]; rfl
  rw [hkids] at hin
  have hk := honestCall_kid hcall hshape hin 1 (J n c0 (J n c1 subj b).label.evaluation c)
    (by simp [evalOrder_s7])
    (by
      intro j k' hj hk'
      rw [evalOrder_s7] at hk'
      rcases j with _ | j
      · simp at hk'; subst hk'; exact g1
      · omega)
  rw [J_subject, J_formula] at hk
  exact hk

/-- **The first child in evaluation order needs nothing** (OP2's children 0/1, OP9's core). -/
theorem honestCall_op9_core {G : NTree (GenComputeRow K)} (n : ℕ)
    (row : (State × DTcomp K) × ℕ) (c0 c1 : NTree ((State × DTcomp K) × ℕ))
    (subj fc : Noun) (a : ℕ) (h : row.1.1 = .s9)
    (hcall : HonestCall G subj (.cell (.atom 9) (.cell (.atom a) fc)))
    (hslot : Noun.slot a (J n c0 subj fc).label.evaluation =
      some (sv .verify_child (row.2 + 3))) :
    HonestCall G subj fc := by
  have hin := kidInputs_op9 (sv := sv) (ax := ax) n row c0 c1 subj fc a h hslot
  have hshape : FormulaShape .s9 (.cell (.atom 9) (.cell (.atom a) fc)) := ⟨a, fc, rfl⟩
  have hkids : (J (n + 1) (.node row [c0, c1]) subj
      (.cell (.atom 9) (.cell (.atom a) fc))).children =
      [J n c0 subj fc, J n c1 (J n c0 subj fc).label.evaluation (sv .verify_child (row.2 + 3))] := by
    rw [J_s9 (sv := sv) (ax := ax) _ _ row c0 c1 h]; rfl
  rw [hkids] at hin
  have hk := honestCall_kid hcall hshape hin 0 (J n c0 subj fc) (by simp [evalOrder_s9])
    (by intro j k' hj; omega)
  rw [J_subject, J_formula] at hk
  exact hk

end Step1



section Receipt

open Nock.Noun

/-- The honest guarded run IS bounded (subject `atom 0`, result `atom 1`), but a MISALIGNED served
value `atom 30` makes the C2 join output `atom 31`, unbounded at `q = 31`; and the tree is provably
not `C2Aligned`. -/
theorem op4_misaligned_under_bounded_run (row4 row0 : (State × DTcomp (ZMod 31)) × ℕ)
    (svq : MState → ℕ → Noun) (axq : ℕ → ℕ)
    (h4 : row4.1.1 = .s4) (h0 : row0.1.1 = .s0)
    (hserve : svq .verify_child (row0.2 + 2) = .atom 30) :
    evalGBy 31 2 (.atom 0) (.cell (.atom 4) (.cell (.atom 0) (.atom 1))) = some (.atom 1) ∧
    (c2JoinFuel (fun l : (State × DTcomp (ZMod 31)) × ℕ => l.1.1) (fun l => l.2) svq axq 2
        (.node row4 [.node row0 []]) (.atom 0) (.cell (.atom 4) (.cell (.atom 0) (.atom 1)))).label.evaluation = .atom 31 ∧
    ¬ BoundedBy 31 (.atom 31) ∧
    ¬ C2Aligned (K := ZMod 31) (sv := svq) (ax := axq) (.node row4 [.node row0 []]) (.atom 0)
        (.cell (.atom 4) (.cell (.atom 0) (.atom 1))) := by
  refine ⟨by simp [evalGBy, lusGBy, slot], ?_, by simp, ?_⟩
  · simp [c2JoinFuel, c2SkeletonRow, c2Evaluation, h4, h0, kidSkel, hserve, nounTail]
  · intro hA
    cases hA with
    | op4 _ hC =>
      cases hC with
      | op0 _ hslot => rw [hserve] at hslot; simp [slot] at hslot

end Receipt

end Nock.RedTeam.Batch1110

#print axioms Nock.RedTeam.Batch1110.good_of_inp
#print axioms Nock.RedTeam.Batch1110.root_good
#print axioms Nock.RedTeam.Batch1110.honestCall_op2_third
#print axioms Nock.RedTeam.Batch1110.honestCall_op9_arm
#print axioms Nock.RedTeam.Batch1110.op4_misaligned_under_bounded_run
