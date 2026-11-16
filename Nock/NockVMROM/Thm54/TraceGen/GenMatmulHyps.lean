/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulHyps.lean

  Tree-local Vcomp hypotheses for the assigned matmul compute tree.
  `NoHead3` forbids opcode-3 cell heads (hereditary on subnouns), which
  is decided on the source `mmFormula` / `mmSubject` and preserved by
  `Noun.slot`.  Generated trees whose formulas stay `NoHead3` have no
  `.s3` nodes, so the OP3 cell-size window is vacuous.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulAccept
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulConfig
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulMem
import Nock.NockVMROM.Thm54.TraceGen.Encode
import Mathlib.Tactic.IntervalCases

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

/-! ## Hereditary “no opcode-3 cell head” -/

def NoHead3 : Noun → Prop
  | .atom _ => True
  | .cell (.atom op) tl => op ≠ 3 ∧ NoHead3 tl
  | .cell (.cell a b) c => NoHead3 (.cell a b) ∧ NoHead3 c

instance instDecidableNoHead3 : (n : Noun) → Decidable (NoHead3 n)
  | .atom _ => isTrue trivial
  | .cell (.atom op) tl =>
    if h : op = 3 then
      isFalse fun hf => hf.1 h
    else
      match instDecidableNoHead3 tl with
      | isTrue htl => isTrue ⟨h, htl⟩
      | isFalse hntl => isFalse fun hf => hntl hf.2
  | .cell (.cell a b) c =>
    match instDecidableNoHead3 (.cell a b), instDecidableNoHead3 c with
    | isTrue hl, isTrue hr => isTrue ⟨hl, hr⟩
    | isFalse hl, _ => isFalse fun hf => hl hf.1
    | _, isFalse hr => isFalse fun hf => hr hf.2

theorem noHead3_atom (k : ℕ) : NoHead3 (.atom k) := trivial

theorem noHead3_not_op3 (tl : Noun) : ¬ NoHead3 (.cell (.atom 3) tl) :=
  fun h => h.1 rfl

theorem noHead3_left {a b : Noun} (h : NoHead3 (.cell a b)) : NoHead3 a := by
  cases a with
  | atom _ => exact trivial
  | cell _ _ => exact h.1

theorem noHead3_right {a b : Noun} (h : NoHead3 (.cell a b)) : NoHead3 b := by
  cases a with
  | atom _ => exact h.2
  | cell _ _ => exact h.2

theorem noHead3_slot {n : Noun} {ax : ℕ} {v : Noun}
    (h : NoHead3 n) (hs : Noun.slot ax n = some v) : NoHead3 v := by
  induction ax using Nat.strongRecOn generalizing n v with
  | ind ax ih =>
    match ax with
    | 0 =>
      simp [Noun.slot] at hs
    | 1 =>
      simp [Noun.slot] at hs
      subst v
      exact h
    | ax + 2 =>
      have hge : 2 ≤ ax + 2 := by omega
      rw [slot_ge_two (ax + 2) n hge] at hs
      cases hmid : Noun.slot ((ax + 2) / 2) n with
      | none =>
        rw [hmid] at hs
        cases hs
      | some mid =>
        have hmid' : NoHead3 mid :=
          ih ((ax + 2) / 2) (by omega) h hmid
        rw [hmid] at hs
        cases mid with
        | atom _ =>
          simp at hs
        | cell l r =>
          simp at hs
          by_cases hmod : ax % 2 = 0
          · simp [hmod] at hs
            subst v
            exact noHead3_left hmid'
          · simp [hmod] at hs
            subst v
            exact noHead3_right hmid'

variable {K : Type} [Field K]

theorem gen_op0_one {fuel : ℕ} {s : Noun} {t : NTree (GenComputeRow K)} {r : Noun}
    (h : genComputeSkeleton (K := K) fuel s (.cell (.atom 0) (.atom 1)) = .ok (t, r)) :
    r = s := by
  cases fuel with
  | zero =>
    simp [genComputeSkeleton] at h
  | succ n =>
    simp [genComputeSkeleton, Noun.slot] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

theorem op3CallSizeOk_of_not_s3 {z : K} {s : ComputeRowSkeleton}
    (h : s.state ≠ State.s3) : s.state = State.s3 → op3CallSizeOk z s :=
  fun hs => (h hs).elim

theorem noHead3_pair {a b : Noun} (ha : NoHead3 a) (hb : NoHead3 b)
    (hne : a ≠ .atom 3) : NoHead3 (.cell a b) := by
  cases a with
  | atom k =>
    have hk : k ≠ 3 := fun h => hne (h ▸ rfl)
    exact ⟨hk, hb⟩
  | cell _ _ =>
    exact ⟨ha, hb⟩

theorem inTree_ne_s3_of_children {lab : GenComputeRow K}
    {cs : List (NTree (GenComputeRow K))}
    (hroot : lab.skel.state ≠ State.s3)
    (hcs : ∀ c ∈ cs, ∀ v, InTree c v → v.label.skel.state ≠ State.s3) :
    ∀ v, InTree (.node lab cs) v → v.label.skel.state ≠ State.s3 := by
  intro v hv
  cases hv with
  | here => exact hroot
  | sub hs hu => exact hcs _ hs _ hu

/-! ## Source-noun cell Dyck -/

def AllCellDyckNe (z : K) : Noun → Prop
  | .atom _ => True
  | .cell a b =>
    (encC z (.cell a b)).dyck ≠ 0 ∧ AllCellDyckNe z a ∧ AllCellDyckNe z b

instance instDecidableAllCellDyckNe [DecidableEq K] (z : K) :
    (n : Noun) → Decidable (AllCellDyckNe z n)
  | .atom _ => isTrue trivial
  | .cell a b =>
    if h : (encC z (.cell a b)).dyck = 0 then
      isFalse fun hf => hf.1 h
    else
      match instDecidableAllCellDyckNe z a, instDecidableAllCellDyckNe z b with
      | isTrue ha, isTrue hb => isTrue ⟨h, ha, hb⟩
      | isFalse ha, _ => isFalse fun hf => ha hf.2.1
      | _, isFalse hb => isFalse fun hf => hb hf.2.2

theorem allCellDyckNe_cell {z : K} {a b : Noun} (h : AllCellDyckNe z (.cell a b)) :
    (encC z (.cell a b)).dyck ≠ 0 :=
  h.1

theorem allCellDyckNe_left {z : K} {a b : Noun} (h : AllCellDyckNe z (.cell a b)) :
    AllCellDyckNe z a :=
  h.2.1

theorem allCellDyckNe_right {z : K} {a b : Noun} (h : AllCellDyckNe z (.cell a b)) :
    AllCellDyckNe z b :=
  h.2.2

theorem allCellDyckNe_cons_head {z : K} {lh lt rtail : Noun}
    (h : AllCellDyckNe z (.cell (.cell lh lt) rtail)) :
    (encC z (.cell lh lt)).dyck ≠ 0 :=
  allCellDyckNe_cell (allCellDyckNe_left h)

/-! ## `φ`-transport of `encC` Dyck -/

theorem hornerLE_map {F K : Type} [Field F] [Field K] (f : F →+* K)
    (z : F) : ∀ l : List F,
    hornerLE (f z) (l.map f) = f (hornerLE z l)
  | [] => by simp [hornerLE, map_zero]
  | a :: l => by
    simp [hornerLE, map_add, map_mul, hornerLE_map f z l]

theorem dyckBits_algebraMap {F K : Type} [Field F] [Field K] [Algebra F K]
    (n : Noun) :
    NPR.dyckBits (K := K) n =
      (NPR.dyckBits (K := F) n).map (algebraMap F K) := by
  simp only [NPR.dyckBits, List.map_map]
  congr 1
  funext b
  cases b <;> simp [RingHom.map_zero, RingHom.map_one]

theorem encC_dyck_algebraMap {F K : Type} [Field F] [Field K] [Algebra F K]
    (z : F) (n : Noun) :
    (encC (algebraMap F K z) n).dyck =
      algebraMap F K (encC z n).dyck := by
  simp [encC_dyck, dyckBits_algebraMap (F := F) (K := K) n,
    hornerLE_map (algebraMap F K) z]

theorem allCellDyckNe_algebraMap {F K : Type} [Field F] [Field K] [Algebra F K]
    {z : F} {n : Noun} (hinj : Function.Injective (algebraMap F K))
    (h : AllCellDyckNe z n) : AllCellDyckNe (algebraMap F K z) n := by
  induction n with
  | atom _ => trivial
  | cell a b iha ihb =>
    refine ⟨?_, iha h.2.1, ihb h.2.2⟩
    rw [encC_dyck_algebraMap]
    exact fun hz => h.1 (hinj (by simpa [map_zero] using hz))

/-! ## OP5 operand atoms -/

theorem op5ResultsAgree_atoms (z : K) {s : ComputeRowSkeleton} {a b : ℕ}
    (ha : P8Census.skeletonSubformula s 0 TripleSlot.result = .atom a)
    (hb : P8Census.skeletonSubformula s 1 TripleSlot.result = .atom b)
    (hne : a ≠ b → (a : K) ≠ (b : K)) :
    op5ResultsAgree z s := by
  unfold op5ResultsAgree
  rw [ha, hb]
  by_cases heq : a = b
  · exact Or.inl (heq ▸ rfl)
  · exact Or.inr (encC_atom_ne z a b (hne heq))

theorem nat_cast_ne_zero_one (_h : (0 : K) ≠ 1) {a b : ℕ}
    (ha : a ≤ 1) (hb : b ≤ 1) : a ≠ b → (a : K) ≠ (b : K) := by
  intro hne
  interval_cases a <;> interval_cases b <;> simp_all

theorem allCellDyckNe_op0 (z : K) (hz : z ≠ 0) (ax : ℕ) :
    AllCellDyckNe z (op0 ax) := by
  refine ⟨?_, trivial, trivial⟩
  simpa [op0] using encC_cell_atom_atom_dyck_ne z hz 0 ax

theorem allCellDyckNe_op1 (z : K) (hz : z ≠ 0) (k : ℕ) :
    AllCellDyckNe z (op1 k) := by
  refine ⟨?_, trivial, trivial⟩
  simpa [op1] using encC_cell_atom_atom_dyck_ne z hz 1 k

theorem allCellDyckNe_cell_atom {z : K} (hz : z ≠ 0) (k : ℕ) {y : Noun}
    (hy : AllCellDyckNe z y)
    (ht : 1 + z * (encC z y).dyck ≠ 0) :
    AllCellDyckNe z (.cell (.atom k) y) := by
  refine ⟨?_, trivial, hy⟩
  rw [encC_cell_atom_dyck z hz k y]
  exact mul_ne_zero hz ht

theorem allCellDyckNe_cons {z : K} {a b : Noun}
    (ha : AllCellDyckNe z a) (hb : AllCellDyckNe z b)
    (hd : (encC z (.cell a b)).dyck ≠ 0) :
    AllCellDyckNe z (.cell a b) :=
  ⟨hd, ha, hb⟩

theorem allCellDyckNe_slot {z : K} {n : Noun} {ax : ℕ} {v : Noun}
    (h : AllCellDyckNe z n) (hs : Noun.slot ax n = some v) :
    AllCellDyckNe z v := by
  induction ax using Nat.strongRecOn generalizing n v with
  | ind ax ih =>
    match ax with
    | 0 =>
      simp [Noun.slot] at hs
    | 1 =>
      simp [Noun.slot] at hs
      subst v
      exact h
    | ax + 2 =>
      have hge : 2 ≤ ax + 2 := by omega
      rw [slot_ge_two (ax + 2) n hge] at hs
      cases hmid : Noun.slot ((ax + 2) / 2) n with
      | none =>
        rw [hmid] at hs
        cases hs
      | some mid =>
        have hmid' : AllCellDyckNe z mid :=
          ih ((ax + 2) / 2) (by omega) h hmid
        rw [hmid] at hs
        cases mid with
        | atom _ =>
          simp at hs
        | cell l r =>
          simp at hs
          by_cases hmod : ax % 2 = 0
          · simp [hmod] at hs
            subst v
            exact allCellDyckNe_left hmid'
          · simp [hmod] at hs
            subst v
            exact allCellDyckNe_right hmid'

/-! ## Source-noun opcode shape -/

/-- No `[2 b c]` cell in the noun, so `genComputeSkeleton` never emits `.s2`. -/
def NoOp2 : Noun → Prop
  | .atom _ => True
  | .cell (.atom op) tl => op ≠ 2 ∧ NoOp2 tl
  | .cell (.cell a b) c => NoOp2 (.cell a b) ∧ NoOp2 c

instance instDecidableNoOp2 : (n : Noun) → Decidable (NoOp2 n)
  | .atom _ => isTrue trivial
  | .cell (.atom op) tl =>
    if h : op = 2 then
      isFalse fun hf => hf.1 h
    else
      match instDecidableNoOp2 tl with
      | isTrue htl => isTrue ⟨h, htl⟩
      | isFalse hntl => isFalse fun hf => hntl hf.2
  | .cell (.cell a b) c =>
    match instDecidableNoOp2 (.cell a b), instDecidableNoOp2 c with
    | isTrue hl, isTrue hr => isTrue ⟨hl, hr⟩
    | isFalse hl, _ => isFalse fun hf => hl hf.1
    | _, isFalse hr => isFalse fun hf => hr hf.2

theorem noOp2_not_op2 (tl : Noun) : ¬ NoOp2 (.cell (.atom 2) tl) :=
  fun h => h.1 rfl

theorem noOp2_left {a b : Noun} (h : NoOp2 (.cell a b)) : NoOp2 a := by
  cases a with
  | atom _ => exact trivial
  | cell _ _ => exact h.1

theorem noOp2_right {a b : Noun} (h : NoOp2 (.cell a b)) : NoOp2 b := by
  cases a with
  | atom _ => exact h.2
  | cell _ _ => exact h.2

theorem noOp2_slot {n : Noun} {ax : ℕ} {v : Noun}
    (h : NoOp2 n) (hs : Noun.slot ax n = some v) : NoOp2 v := by
  induction ax using Nat.strongRecOn generalizing n v with
  | ind ax ih =>
    match ax with
    | 0 =>
      simp [Noun.slot] at hs
    | 1 =>
      simp [Noun.slot] at hs
      subst v
      exact h
    | ax + 2 =>
      have hge : 2 ≤ ax + 2 := by omega
      rw [slot_ge_two (ax + 2) n hge] at hs
      cases hmid : Noun.slot ((ax + 2) / 2) n with
      | none =>
        rw [hmid] at hs
        cases hs
      | some mid =>
        have hmid' : NoOp2 mid :=
          ih ((ax + 2) / 2) (by omega) h hmid
        rw [hmid] at hs
        cases mid with
        | atom _ =>
          simp at hs
        | cell l r =>
          simp at hs
          by_cases hmod : ax % 2 = 0
          · simp [hmod] at hs
            subst v
            exact noOp2_left hmid'
          · simp [hmod] at hs
            subst v
            exact noOp2_right hmid'

/-- Every `OP_9` in the noun is `invokeAxis` (`[9 [ax [0 1]]]`). -/
def AllOp9Invoke : Noun → Prop
  | .atom _ => True
  | .cell (.atom 9) (.cell (.atom _) c) =>
      c = .cell (.atom 0) (.atom 1) ∧ AllOp9Invoke c
  | .cell (.atom 9) _ => False
  | .cell (.atom _) tl => AllOp9Invoke tl
  | .cell (.cell a b) c => AllOp9Invoke (.cell a b) ∧ AllOp9Invoke c

instance instDecidableAllOp9Invoke : (n : Noun) → Decidable (AllOp9Invoke n)
  | .atom _ => isTrue trivial
  | .cell (.atom op) tl =>
    if hop : op = 9 then
      match tl with
      | .atom _ => isFalse fun hf => (by subst hop; exact hf)
      | .cell (.atom _) c =>
        if h : c = .cell (.atom 0) (.atom 1) then
          match instDecidableAllOp9Invoke c with
          | isTrue hc => isTrue (by subst hop; exact ⟨h, hc⟩)
          | isFalse hnc => isFalse fun hf => by
              subst hop
              exact hnc hf.2
        else
          isFalse fun hf => by
            subst hop
            exact h hf.1
      | .cell (.cell _ _) _ => isFalse fun hf => (by subst hop; exact hf)
    else
      match op, instDecidableAllOp9Invoke tl with
      | 9, _ => (hop rfl).elim
      | 0, isTrue htl => isTrue htl
      | 0, isFalse hntl => isFalse hntl
      | 1, isTrue htl => isTrue htl
      | 1, isFalse hntl => isFalse hntl
      | 2, isTrue htl => isTrue htl
      | 2, isFalse hntl => isFalse hntl
      | 3, isTrue htl => isTrue htl
      | 3, isFalse hntl => isFalse hntl
      | 4, isTrue htl => isTrue htl
      | 4, isFalse hntl => isFalse hntl
      | 5, isTrue htl => isTrue htl
      | 5, isFalse hntl => isFalse hntl
      | 6, isTrue htl => isTrue htl
      | 6, isFalse hntl => isFalse hntl
      | 7, isTrue htl => isTrue htl
      | 7, isFalse hntl => isFalse hntl
      | 8, isTrue htl => isTrue htl
      | 8, isFalse hntl => isFalse hntl
      | k + 10, isTrue htl => isTrue htl
      | k + 10, isFalse hntl => isFalse hntl
  | .cell (.cell a b) c =>
    match instDecidableAllOp9Invoke (.cell a b), instDecidableAllOp9Invoke c with
    | isTrue hl, isTrue hr => isTrue ⟨hl, hr⟩
    | isFalse hl, _ => isFalse fun hf => hl hf.1
    | _, isFalse hr => isFalse fun hf => hr hf.2

theorem allOp9Invoke_op9 {ax : ℕ} {c : Noun}
    (h : AllOp9Invoke (.cell (.atom 9) (.cell (.atom ax) c))) :
    c = .cell (.atom 0) (.atom 1) :=
  h.1

theorem allOp9Invoke_op9_core {ax : ℕ} {c : Noun}
    (h : AllOp9Invoke (.cell (.atom 9) (.cell (.atom ax) c))) :
    AllOp9Invoke c :=
  h.2

theorem allOp9Invoke_cons_left {a b c : Noun}
    (h : AllOp9Invoke (.cell (.cell a b) c)) : AllOp9Invoke (.cell a b) :=
  h.1

theorem allOp9Invoke_cons_right {a b c : Noun}
    (h : AllOp9Invoke (.cell (.cell a b) c)) : AllOp9Invoke c :=
  h.2

theorem allOp9Invoke_left {a b : Noun} (h : AllOp9Invoke (.cell a b)) :
    AllOp9Invoke a := by
  cases a with
  | atom _ => exact trivial
  | cell _ _ => exact h.1

/-- Hereditary “no atom 3”, so OP1/OP0 never return `.atom 3`. -/
def NoAtom3 : Noun → Prop
  | .atom k => k ≠ 3
  | .cell a b => NoAtom3 a ∧ NoAtom3 b

instance instDecidableNoAtom3 : (n : Noun) → Decidable (NoAtom3 n)
  | .atom k => inferInstanceAs (Decidable (k ≠ 3))
  | .cell a b =>
    match instDecidableNoAtom3 a, instDecidableNoAtom3 b with
    | isTrue ha, isTrue hb => isTrue ⟨ha, hb⟩
    | isFalse ha, _ => isFalse fun hf => ha hf.1
    | _, isFalse hb => isFalse fun hf => hb hf.2

theorem noAtom3_ne {k : ℕ} (h : NoAtom3 (.atom k)) : k ≠ 3 := h

theorem noAtom3_left {a b : Noun} (h : NoAtom3 (.cell a b)) : NoAtom3 a := h.1

theorem noAtom3_right {a b : Noun} (h : NoAtom3 (.cell a b)) : NoAtom3 b := h.2

theorem noAtom3_slot {n : Noun} {ax : ℕ} {v : Noun}
    (h : NoAtom3 n) (hs : Noun.slot ax n = some v) : NoAtom3 v := by
  induction ax using Nat.strongRecOn generalizing n v with
  | ind ax ih =>
    match ax with
    | 0 =>
      simp [Noun.slot] at hs
    | 1 =>
      simp [Noun.slot] at hs
      subst v
      exact h
    | ax + 2 =>
      have hge : 2 ≤ ax + 2 := by omega
      rw [slot_ge_two (ax + 2) n hge] at hs
      cases hmid : Noun.slot ((ax + 2) / 2) n with
      | none =>
        rw [hmid] at hs
        cases hs
      | some mid =>
        have hmid' : NoAtom3 mid :=
          ih ((ax + 2) / 2) (by omega) h hmid
        rw [hmid] at hs
        cases mid with
        | atom _ =>
          simp at hs
        | cell l r =>
          simp at hs
          by_cases hmod : ax % 2 = 0
          · simp [hmod] at hs
            subst v
            exact noAtom3_left hmid'
          · simp [hmod] at hs
            subst v
            exact noAtom3_right hmid'

theorem formulaHead_cons_dyck {z : K} {lh lt rtail : Noun}
    (h : AllCellDyckNe z (.cell (.cell lh lt) rtail)) :
    (encC z (formulaHead (.cell (.cell lh lt) rtail))).dyck ≠ 0 := by
  simpa [formulaHead] using allCellDyckNe_cons_head h

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open ComputeTable

theorem mmFormula_noHead3 : NoHead3 mmFormula := by decide
theorem mmSubject_noHead3 : NoHead3 mmSubject := by decide
theorem addArm_noHead3 : NoHead3 addArm := by decide
theorem macArm_noHead3 : NoHead3 macArm := by decide
theorem mmBattery_noHead3 : NoHead3 mmBattery := by decide

theorem mmSubject_noOp2 : NoOp2 mmSubject := by decide

theorem mmFormula_allOp9Invoke : AllOp9Invoke mmFormula := by decide
theorem addArm_allOp9Invoke : AllOp9Invoke addArm := by decide
theorem macArm_allOp9Invoke : AllOp9Invoke macArm := by decide
theorem mmBattery_allOp9Invoke : AllOp9Invoke mmBattery := by decide

theorem mmFormula_noAtom3 : NoAtom3 mmFormula := by decide
theorem mmSubject_noAtom3 : NoAtom3 mmSubject := by decide
theorem addArm_noAtom3 : NoAtom3 addArm := by decide
theorem macArm_noAtom3 : NoAtom3 macArm := by decide
theorem mmBattery_noAtom3 : NoAtom3 mmBattery := by decide

theorem z8_ne_zero : (8 : F) ≠ 0 := by decide

set_option maxRecDepth 100000

theorem mmSubject_allCellDyckNe_base : AllCellDyckNe (8 : F) mmSubject := by decide

theorem addArm_allCellDyckNe_base : AllCellDyckNe (8 : F) addArm := by
  have hz := z8_ne_zero
  have h14 := allCellDyckNe_op0 (8 : F) hz 14
  have h15 := allCellDyckNe_op0 (8 : F) hz 15
  have h6 := allCellDyckNe_op0 (8 : F) hz 6
  have h2 := allCellDyckNe_op0 (8 : F) hz 2
  have hop5t : AllCellDyckNe (8 : F) (.cell (op0 14) (op0 15)) :=
    allCellDyckNe_cons h14 h15 (by decide)
  have hop5 : AllCellDyckNe (8 : F) (op5 (op0 14) (op0 15)) := by
    simpa [op5] using
      allCellDyckNe_cell_atom hz 5 hop5t (by decide)
  have hop4a : AllCellDyckNe (8 : F) (op4 (op0 6)) := by
    simpa [op4] using
      allCellDyckNe_cell_atom hz 4 h6 (by decide)
  have hop4i : AllCellDyckNe (8 : F) (op4 (op0 14)) := by
    simpa [op4] using
      allCellDyckNe_cell_atom hz 4 h14 (by decide)
  have hinner : AllCellDyckNe (8 : F) (.cell (op4 (op0 14)) (op0 15)) :=
    allCellDyckNe_cons hop4i h15 (by decide)
  have hns : AllCellDyckNe (8 : F) addNewSample := by
    simpa [addNewSample] using allCellDyckNe_cons hop4a hinner (by decide)
  have hpair : AllCellDyckNe (8 : F) (.cell (op0 2) addNewSample) :=
    allCellDyckNe_cons h2 hns (by decide)
  have hinv : AllCellDyckNe (8 : F) (invokeAxis 2) := by
    have hc : AllCellDyckNe (8 : F) (.cell (.atom 2) (op0 1)) :=
      allCellDyckNe_cell_atom hz 2 (allCellDyckNe_op0 (8 : F) hz 1)
        (by decide)
    simpa [invokeAxis, op0] using
      allCellDyckNe_cell_atom hz 9 hc (by decide)
  have hslam : AllCellDyckNe (8 : F) (slam (op0 2) addNewSample 2) := by
    simpa [slam, op7] using
      allCellDyckNe_cell_atom hz 7
        (allCellDyckNe_cons hpair hinv (by decide)) (by decide)
  have hbr : AllCellDyckNe (8 : F) (.cell (op0 6) (slam (op0 2) addNewSample 2)) :=
    allCellDyckNe_cons h6 hslam (by decide)
  have htail : AllCellDyckNe (8 : F)
      (.cell (op5 (op0 14) (op0 15))
        (.cell (op0 6) (slam (op0 2) addNewSample 2))) :=
    allCellDyckNe_cons hop5 hbr (by decide)
  simpa [addArm, op6] using
    allCellDyckNe_cell_atom hz 6 htail (by decide)

theorem mmSubject_allCellDyckNe : AllCellDyckNe seedZ mmSubject :=
  allCellDyckNe_algebraMap φ_injective mmSubject_allCellDyckNe_base
theorem addArm_allCellDyckNe : AllCellDyckNe seedZ addArm :=
  allCellDyckNe_algebraMap φ_injective addArm_allCellDyckNe_base

theorem invokeAxis2_allCellDyckNe_base : AllCellDyckNe (8 : F) (invokeAxis 2) := by
  have hz := z8_ne_zero
  have hc : AllCellDyckNe (8 : F) (.cell (.atom 2) (op0 1)) :=
    allCellDyckNe_cell_atom hz 2 (allCellDyckNe_op0 (8 : F) hz 1) (by decide)
  simpa [invokeAxis, op0] using allCellDyckNe_cell_atom hz 9 hc (by decide)

theorem invokeAxis4_allCellDyckNe_base : AllCellDyckNe (8 : F) (invokeAxis 4) := by
  have hz := z8_ne_zero
  have hc : AllCellDyckNe (8 : F) (.cell (.atom 4) (op0 1)) :=
    allCellDyckNe_cell_atom hz 4 (allCellDyckNe_op0 (8 : F) hz 1) (by decide)
  simpa [invokeAxis, op0] using allCellDyckNe_cell_atom hz 9 hc (by decide)

theorem addFromMac_allCellDyckNe_base : AllCellDyckNe (8 : F) addFromMac := by
  have hz := z8_ne_zero
  have h5 := allCellDyckNe_op0 (8 : F) hz 5
  have h6 := allCellDyckNe_op0 (8 : F) hz 6
  have h31 := allCellDyckNe_op0 (8 : F) hz 31
  have hq0 := allCellDyckNe_op1 (8 : F) hz 0
  have hinn : AllCellDyckNe (8 : F) (.cell (op1 0) (op0 31)) :=
    allCellDyckNe_cons hq0 h31 (by decide)
  have hsamp : AllCellDyckNe (8 : F) (.cell (op0 6) (.cell (op1 0) (op0 31))) :=
    allCellDyckNe_cons h6 hinn (by decide)
  have hpair : AllCellDyckNe (8 : F)
      (.cell (op0 5) (.cell (op0 6) (.cell (op1 0) (op0 31)))) :=
    allCellDyckNe_cons h5 hsamp (by decide)
  simpa [addFromMac, slam, op7] using
    allCellDyckNe_cell_atom hz 7
      (allCellDyckNe_cons hpair invokeAxis2_allCellDyckNe_base (by decide))
      (by decide)

theorem macNewSample_allCellDyckNe_base : AllCellDyckNe (8 : F) macNewSample := by
  have hz := z8_ne_zero
  have h14 := allCellDyckNe_op0 (8 : F) hz 14
  have h30 := allCellDyckNe_op0 (8 : F) hz 30
  have h31 := allCellDyckNe_op0 (8 : F) hz 31
  have hop4 : AllCellDyckNe (8 : F) (op4 (op0 14)) := by
    simpa [op4] using allCellDyckNe_cell_atom hz 4 h14 (by decide)
  have hnm : AllCellDyckNe (8 : F) (.cell (op0 30) (op0 31)) :=
    allCellDyckNe_cons h30 h31 (by decide)
  have hrest : AllCellDyckNe (8 : F) (.cell (op4 (op0 14)) (.cell (op0 30) (op0 31))) :=
    allCellDyckNe_cons hop4 hnm (by decide)
  simpa [macNewSample] using
    allCellDyckNe_cons addFromMac_allCellDyckNe_base hrest (by decide)

theorem macArm_allCellDyckNe_base : AllCellDyckNe (8 : F) macArm := by
  have hz := z8_ne_zero
  have h14 := allCellDyckNe_op0 (8 : F) hz 14
  have h30 := allCellDyckNe_op0 (8 : F) hz 30
  have h6 := allCellDyckNe_op0 (8 : F) hz 6
  have h2 := allCellDyckNe_op0 (8 : F) hz 2
  have hop5t : AllCellDyckNe (8 : F) (.cell (op0 14) (op0 30)) :=
    allCellDyckNe_cons h14 h30 (by decide)
  have hop5 : AllCellDyckNe (8 : F) (op5 (op0 14) (op0 30)) := by
    simpa [op5] using allCellDyckNe_cell_atom hz 5 hop5t (by decide)
  have hpair : AllCellDyckNe (8 : F) (.cell (op0 2) macNewSample) :=
    allCellDyckNe_cons h2 macNewSample_allCellDyckNe_base (by decide)
  have hslam : AllCellDyckNe (8 : F) (slam (op0 2) macNewSample 4) := by
    simpa [slam, op7] using
      allCellDyckNe_cell_atom hz 7
        (allCellDyckNe_cons hpair invokeAxis4_allCellDyckNe_base (by decide))
        (by decide)
  have hbr : AllCellDyckNe (8 : F) (.cell (op0 6) (slam (op0 2) macNewSample 4)) :=
    allCellDyckNe_cons h6 hslam (by decide)
  have htail : AllCellDyckNe (8 : F)
      (.cell (op5 (op0 14) (op0 30))
        (.cell (op0 6) (slam (op0 2) macNewSample 4))) :=
    allCellDyckNe_cons hop5 hbr (by decide)
  simpa [macArm, op6] using allCellDyckNe_cell_atom hz 6 htail (by decide)

theorem mmBattery_allCellDyckNe_base : AllCellDyckNe (8 : F) mmBattery := by
  simpa [mmBattery] using
    allCellDyckNe_cons macArm_allCellDyckNe_base addArm_allCellDyckNe_base (by decide)

theorem macArm_allCellDyckNe : AllCellDyckNe seedZ macArm :=
  allCellDyckNe_algebraMap φ_injective macArm_allCellDyckNe_base
theorem mmBattery_allCellDyckNe : AllCellDyckNe seedZ mmBattery :=
  allCellDyckNe_algebraMap φ_injective mmBattery_allCellDyckNe_base

theorem quote_mmBattery_allCellDyckNe_base :
    AllCellDyckNe (8 : F) (quote mmBattery) := by
  simpa [quote] using
    allCellDyckNe_cell_atom z8_ne_zero 1 mmBattery_allCellDyckNe_base (by decide)

theorem mmC00_allCellDyckNe_base : AllCellDyckNe (8 : F) mmC00 := by
  have hz := z8_ne_zero
  have h0 := allCellDyckNe_op1 (8 : F) hz 0
  have h8 := allCellDyckNe_op0 (8 : F) hz 8
  have h12 := allCellDyckNe_op0 (8 : F) hz 12
  have h9 := allCellDyckNe_op0 (8 : F) hz 9
  have h14 := allCellDyckNe_op0 (8 : F) hz 14
  have hnm : AllCellDyckNe (8 : F) (.cell (op0 8) (op0 12)) :=
    allCellDyckNe_cons h8 h12 (by decide)
  have hrest : AllCellDyckNe (8 : F) (.cell (op1 0) (.cell (op0 8) (op0 12))) :=
    allCellDyckNe_cons h0 hnm (by decide)
  have hsamp : AllCellDyckNe (8 : F)
      (.cell (op1 0) (.cell (op1 0) (.cell (op0 8) (op0 12)))) :=
    allCellDyckNe_cons h0 hrest (by decide)
  have hinn : AllCellDyckNe (8 : F)
      (invokeMac (op1 0) (op0 8) (op0 12)) := by
    have hpair := allCellDyckNe_cons quote_mmBattery_allCellDyckNe_base hsamp
      (by decide)
    simpa [invokeMac, slam, op7] using
      allCellDyckNe_cell_atom hz 7
        (allCellDyckNe_cons hpair invokeAxis4_allCellDyckNe_base (by decide))
        (by decide)
  have hnm' : AllCellDyckNe (8 : F) (.cell (op0 9) (op0 14)) :=
    allCellDyckNe_cons h9 h14 (by decide)
  have hrest' : AllCellDyckNe (8 : F) (.cell (op1 0) (.cell (op0 9) (op0 14))) :=
    allCellDyckNe_cons h0 hnm' (by decide)
  have hsamp' : AllCellDyckNe (8 : F)
      (.cell (invokeMac (op1 0) (op0 8) (op0 12))
        (.cell (op1 0) (.cell (op0 9) (op0 14)))) :=
    allCellDyckNe_cons hinn hrest' (by decide)
  simpa [mmC00, mac2, invokeMac, slam, op7] using
    allCellDyckNe_cell_atom hz 7
      (allCellDyckNe_cons
        (allCellDyckNe_cons quote_mmBattery_allCellDyckNe_base hsamp' (by decide))
        invokeAxis4_allCellDyckNe_base (by decide))
      (by decide)

theorem mmC01_allCellDyckNe_base : AllCellDyckNe (8 : F) mmC01 := by
  have hz := z8_ne_zero
  have h0 := allCellDyckNe_op1 (8 : F) hz 0
  have h8 := allCellDyckNe_op0 (8 : F) hz 8
  have h13 := allCellDyckNe_op0 (8 : F) hz 13
  have h9 := allCellDyckNe_op0 (8 : F) hz 9
  have h15 := allCellDyckNe_op0 (8 : F) hz 15
  have hnm : AllCellDyckNe (8 : F) (.cell (op0 8) (op0 13)) :=
    allCellDyckNe_cons h8 h13 (by decide)
  have hrest : AllCellDyckNe (8 : F) (.cell (op1 0) (.cell (op0 8) (op0 13))) :=
    allCellDyckNe_cons h0 hnm (by decide)
  have hsamp : AllCellDyckNe (8 : F)
      (.cell (op1 0) (.cell (op1 0) (.cell (op0 8) (op0 13)))) :=
    allCellDyckNe_cons h0 hrest (by decide)
  have hinn : AllCellDyckNe (8 : F)
      (invokeMac (op1 0) (op0 8) (op0 13)) := by
    have hpair := allCellDyckNe_cons quote_mmBattery_allCellDyckNe_base hsamp
      (by decide)
    simpa [invokeMac, slam, op7] using
      allCellDyckNe_cell_atom hz 7
        (allCellDyckNe_cons hpair invokeAxis4_allCellDyckNe_base (by decide))
        (by decide)
  have hnm' : AllCellDyckNe (8 : F) (.cell (op0 9) (op0 15)) :=
    allCellDyckNe_cons h9 h15 (by decide)
  have hrest' : AllCellDyckNe (8 : F) (.cell (op1 0) (.cell (op0 9) (op0 15))) :=
    allCellDyckNe_cons h0 hnm' (by decide)
  have hsamp' : AllCellDyckNe (8 : F)
      (.cell (invokeMac (op1 0) (op0 8) (op0 13))
        (.cell (op1 0) (.cell (op0 9) (op0 15)))) :=
    allCellDyckNe_cons hinn hrest' (by decide)
  simpa [mmC01, mac2, invokeMac, slam, op7] using
    allCellDyckNe_cell_atom hz 7
      (allCellDyckNe_cons
        (allCellDyckNe_cons quote_mmBattery_allCellDyckNe_base hsamp' (by decide))
        invokeAxis4_allCellDyckNe_base (by decide))
      (by decide)

theorem mmC10_allCellDyckNe_base : AllCellDyckNe (8 : F) mmC10 := by
  have hz := z8_ne_zero
  have h0 := allCellDyckNe_op1 (8 : F) hz 0
  have h10 := allCellDyckNe_op0 (8 : F) hz 10
  have h12 := allCellDyckNe_op0 (8 : F) hz 12
  have h11 := allCellDyckNe_op0 (8 : F) hz 11
  have h14 := allCellDyckNe_op0 (8 : F) hz 14
  have hnm : AllCellDyckNe (8 : F) (.cell (op0 10) (op0 12)) :=
    allCellDyckNe_cons h10 h12 (by decide)
  have hrest : AllCellDyckNe (8 : F) (.cell (op1 0) (.cell (op0 10) (op0 12))) :=
    allCellDyckNe_cons h0 hnm (by decide)
  have hsamp : AllCellDyckNe (8 : F)
      (.cell (op1 0) (.cell (op1 0) (.cell (op0 10) (op0 12)))) :=
    allCellDyckNe_cons h0 hrest (by decide)
  have hinn : AllCellDyckNe (8 : F)
      (invokeMac (op1 0) (op0 10) (op0 12)) := by
    have hpair := allCellDyckNe_cons quote_mmBattery_allCellDyckNe_base hsamp
      (by decide)
    simpa [invokeMac, slam, op7] using
      allCellDyckNe_cell_atom hz 7
        (allCellDyckNe_cons hpair invokeAxis4_allCellDyckNe_base (by decide))
        (by decide)
  have hnm' : AllCellDyckNe (8 : F) (.cell (op0 11) (op0 14)) :=
    allCellDyckNe_cons h11 h14 (by decide)
  have hrest' : AllCellDyckNe (8 : F) (.cell (op1 0) (.cell (op0 11) (op0 14))) :=
    allCellDyckNe_cons h0 hnm' (by decide)
  have hsamp' : AllCellDyckNe (8 : F)
      (.cell (invokeMac (op1 0) (op0 10) (op0 12))
        (.cell (op1 0) (.cell (op0 11) (op0 14)))) :=
    allCellDyckNe_cons hinn hrest' (by decide)
  simpa [mmC10, mac2, invokeMac, slam, op7] using
    allCellDyckNe_cell_atom hz 7
      (allCellDyckNe_cons
        (allCellDyckNe_cons quote_mmBattery_allCellDyckNe_base hsamp' (by decide))
        invokeAxis4_allCellDyckNe_base (by decide))
      (by decide)

theorem mmC11_allCellDyckNe_base : AllCellDyckNe (8 : F) mmC11 := by
  have hz := z8_ne_zero
  have h0 := allCellDyckNe_op1 (8 : F) hz 0
  have h10 := allCellDyckNe_op0 (8 : F) hz 10
  have h13 := allCellDyckNe_op0 (8 : F) hz 13
  have h11 := allCellDyckNe_op0 (8 : F) hz 11
  have h15 := allCellDyckNe_op0 (8 : F) hz 15
  have hnm : AllCellDyckNe (8 : F) (.cell (op0 10) (op0 13)) :=
    allCellDyckNe_cons h10 h13 (by decide)
  have hrest : AllCellDyckNe (8 : F) (.cell (op1 0) (.cell (op0 10) (op0 13))) :=
    allCellDyckNe_cons h0 hnm (by decide)
  have hsamp : AllCellDyckNe (8 : F)
      (.cell (op1 0) (.cell (op1 0) (.cell (op0 10) (op0 13)))) :=
    allCellDyckNe_cons h0 hrest (by decide)
  have hinn : AllCellDyckNe (8 : F)
      (invokeMac (op1 0) (op0 10) (op0 13)) := by
    have hpair := allCellDyckNe_cons quote_mmBattery_allCellDyckNe_base hsamp
      (by decide)
    simpa [invokeMac, slam, op7] using
      allCellDyckNe_cell_atom hz 7
        (allCellDyckNe_cons hpair invokeAxis4_allCellDyckNe_base (by decide))
        (by decide)
  have hnm' : AllCellDyckNe (8 : F) (.cell (op0 11) (op0 15)) :=
    allCellDyckNe_cons h11 h15 (by decide)
  have hrest' : AllCellDyckNe (8 : F) (.cell (op1 0) (.cell (op0 11) (op0 15))) :=
    allCellDyckNe_cons h0 hnm' (by decide)
  have hsamp' : AllCellDyckNe (8 : F)
      (.cell (invokeMac (op1 0) (op0 10) (op0 13))
        (.cell (op1 0) (.cell (op0 11) (op0 15)))) :=
    allCellDyckNe_cons hinn hrest' (by decide)
  simpa [mmC11, mac2, invokeMac, slam, op7] using
    allCellDyckNe_cell_atom hz 7
      (allCellDyckNe_cons
        (allCellDyckNe_cons quote_mmBattery_allCellDyckNe_base hsamp' (by decide))
        invokeAxis4_allCellDyckNe_base (by decide))
      (by decide)

theorem mmFormula_allCellDyckNe_base : AllCellDyckNe (8 : F) mmFormula := by
  have hL : AllCellDyckNe (8 : F) (.cell mmC00 mmC01) :=
    allCellDyckNe_cons mmC00_allCellDyckNe_base mmC01_allCellDyckNe_base (by decide)
  have hR : AllCellDyckNe (8 : F) (.cell mmC10 mmC11) :=
    allCellDyckNe_cons mmC10_allCellDyckNe_base mmC11_allCellDyckNe_base (by decide)
  simpa [mmFormula] using allCellDyckNe_cons hL hR (by decide)

theorem mmC00_allCellDyckNe : AllCellDyckNe seedZ mmC00 :=
  allCellDyckNe_algebraMap φ_injective mmC00_allCellDyckNe_base
theorem mmFormula_allCellDyckNe : AllCellDyckNe seedZ mmFormula :=
  allCellDyckNe_algebraMap φ_injective mmFormula_allCellDyckNe_base

end Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

#print axioms Nock.NockVMROM.Thm54.TraceGen.noHead3_slot
#print axioms Nock.NockVMROM.Thm54.TraceGen.allCellDyckNe_slot
#print axioms Nock.NockVMROM.Thm54.TraceGen.noAtom3_slot
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.mmFormula_noHead3
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.mmFormula_allOp9Invoke
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.mmFormula_noAtom3
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.mmFormula_allCellDyckNe
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.addArm_allCellDyckNe
