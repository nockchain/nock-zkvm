/-
  The **Compute Table** of NockVM (paper Appendix B.1), modeled as a full, degree-tracked AIR constraint object (`RAPcomp`),
  together with the algorithmic verifier `Vcomp`,
  and the proof of **`Lem:equiv_compute`**: the RAP admits a satisfying
  assignment iff the algorithmic verifier accepts.

  The AIR is modeled faithfully as concrete polynomial-constraint `Prop`s over
  the extension field `K`, not as abstract predicates.  Each constraint is labelled with its
  constraint name in the paper (SV2, EC.3.4,...).  The fingerprints are the NPR triples of `Nock/NPR.lean`
  (`(size, dyck, leaf)`); the field layer is `Nock/Field.lean`.  Everything
  is generic over an arbitrary field `K` — `goldilocks_prime` is NOT used.

  ─────────────────────────────────────────────────────────────────────────────────────────
  MODELING NOTES / FAITHFULNESS:

  * **Labels are fingerprint triples over `K`.**  `LT_comp = OP × ((N^λ,N^λ),N^λ)`;
    each `N^λ(F)` is represented by its NPR fingerprint `FP = (size, dyck, leaf)`.
    `⊥` / "unused" evaluation slots are the zero fingerprint `0 = (0,0,0)`.  A table `⊥` entry means "no constraint" and is simply omitted.

  * **State = one-hot opcodes.**  The arithmetic state is the one-hot selector vector
    `op : State → K`; we take it to be `opSel pub.state`, the one-hot
    encoding of the label's `state`.  SV constraints 2–3
    are then satisfied automatically (`opSel_boolean`, `opSel_oneHot`), and the content of the
    State-Variables block is constraints 4–6, which tie the formula head `f_h` to `state`
    (`SV_pins_head`).  This faithfully captures `RAP_comp`'s satisfying assignments: by SV2–3
    the only satisfying `op` vectors are exactly the one-hots `{opSel st | st}`.

  * **`Vcomp` is organized by `state`.**  Algorithm NockCompute branches on `formula_head`
    (`f_h`) and, in each branch, checks `state = OP_k`.
    We index `Vcomp` by `state` instead, and put the algorithm's "`f_h` has shape …" test as the
    per-state guard (`f_h = atomFP z k`, resp. `f_h.dyck ≠ 0`).  This is the identical accept
    set — the algorithm accepts iff exactly one (state, f_h-shape) pair is consistent — with the
    per-case checks transcribed line-by-line from the algorithm.
  ─────────────────────────────────────────────────────────────────────────────────────────
-/
import Nock.NPR
import Nock.Field

namespace Nock
namespace ComputeTable

open Classical
attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K]

/-! ## Fingerprint triples and their operations -/

/-- A **fingerprint triple** `(size, dyck, leaf) ∈ K³`.  This is the NPR of a
    noun (`Nock.NPR.fn`) evaluated at the seed `z`: `size = z^λ`, `dyck = F_w(z)`,
    `leaf = F_d(z)`. -/
structure FP (K : Type*) where
  size : K
  dyck : K
  leaf : K

namespace FP

omit [Field K] in
@[ext] theorem ext {a b : FP K} (hs : a.size = b.size) (hd : a.dyck = b.dyck)
    (hl : a.leaf = b.leaf) : a = b := by
  cases a; cases b; simp_all

instance : Zero (FP K) := ⟨⟨0, 0, 0⟩⟩

@[simp] theorem zero_size : (0 : FP K).size = 0 := rfl
@[simp] theorem zero_dyck : (0 : FP K).dyck = 0 := rfl
@[simp] theorem zero_leaf : (0 : FP K).leaf = 0 := rfl

/-- The fingerprint of an **atom** with leaf-value `v`: `size = z` (`= z^1`, one leaf),
    `dyck = 0` (empty Dyck word), `leaf = v` (the fingerprint `(z,0,v)` of an atom). -/
def atomFP (z v : K) : FP K := ⟨z, 0, v⟩

@[simp] theorem atomFP_size (z v : K) : (atomFP z v).size = z := rfl
@[simp] theorem atomFP_dyck (z v : K) : (atomFP z v).dyck = 0 := rfl
@[simp] theorem atomFP_leaf (z v : K) : (atomFP z v).leaf = v := rfl

/-- **`cons` on fingerprints**.
    Combines head `a` and tail `b` into the fingerprint of the cell `[a b]`, using the three
    NPR identities (`Phi1_cons`/`Phi2_cons`/`Phi3_cons` of `Nock/NPR.lean`, with the seed `z`
    in the role of the indeterminate `X` and `a.size = z^{λ_a}`):
      size = `a.size · b.size`
      leaf = `a.leaf + a.size · b.leaf`
      dyck = `z·a.dyck + a.size²·z⁻¹ + a.size²·b.dyck`         (`Φ₃`, corrected — see NPR.lean)
    (The `Φ₃` term `z^{2λ_a−1} = a.size²·z⁻¹` uses `z ≠ 0`; the equivalence `Lem:equiv_compute`
    does not depend on the internal dyck formula, since `cons` is used identically on both
    sides.) -/
def cons (z : K) (a b : FP K) : FP K :=
  ⟨ a.size * b.size,
    z * a.dyck + a.size * a.size * z⁻¹ + a.size * a.size * b.dyck,
    a.leaf + a.size * b.leaf ⟩

/-- Nock `?` (cell test) on a fingerprint: `1` for an atom (`size = z`, one leaf), `0` for a
    cell. -/
noncomputable def qm (z : K) (x : FP K) : K := if x.size = z then 1 else 0

/-- Nock `+` (increment) on an atom fingerprint: leaf `+ 1`, result an atom. -/
def inc (z : K) (x : FP K) : FP K := ⟨z, 0, x.leaf + 1⟩

/-- Nock `=` (equality) on fingerprints: `0` if equal, `1` if not. -/
noncomputable def eqOp (x y : FP K) : K := if x = y then 0 else 1

/-- Scalar multiple of a fingerprint. -/
def smul (c : K) (x : FP K) : FP K := ⟨c * x.size, c * x.dyck, c * x.leaf⟩

/-- Sum of fingerprints (componentwise), used by the OP_6 branch expression. -/
def add (x y : FP K) : FP K := ⟨x.size + y.size, x.dyck + y.dyck, x.leaf + y.leaf⟩

end FP

/-! ## Memory records -/

/-- A **memory record** `((root, child), axis, timestamp)`: `root`/`child` are
    fingerprints, `axis ∈ 𝔽`, `timestamp ∈ K`.  (We keep `axis` in `K` for uniformity; it is
    always a leaf value or a small constant.)  Form R: `axis` hosts `T`; `C'` is `Pub.cprime`
    until the 9-wide `encRec` retype. -/
structure MemRec (K : Type*) where
  root  : FP K
  child : FP K
  axis  : K
  ts    : K

namespace MemRec
omit [Field K] in
@[ext] theorem ext {a b : MemRec K} (hr : a.root = b.root) (hc : a.child = b.child)
    (ha : a.axis = b.axis) (ht : a.ts = b.ts) : a = b := by cases a; cases b; simp_all

/-- The all-zero record `(0,0,0,0)`. -/
def zero : MemRec K := ⟨0, 0, 0, 0⟩
end MemRec

/-! ## The compute state -/

/-- The compute-table state: opcodes `OP_0 … OP_9` plus `cons` (`= op_11`).  Opcode 10 is
    **excluded**. -/
inductive State
  | s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9 | cons
deriving DecidableEq, Repr

namespace State
/-- The numeric opcode value `0..9` (`cons` ↦ 0, unused). -/
def toNat : State → ℕ
  | s0 => 0 | s1 => 1 | s2 => 2 | s3 => 3 | s4 => 4 | s5 => 5
  | s6 => 6 | s7 => 7 | s8 => 8 | s9 => 9 | cons => 0
end State

/-! ## RAP inputs -/

/-- The RAP's initial inputs `(α, z, a, b, c)`: `α` seeds the memory timestamps, `a,b,c` the equality
    RLC, `z` the NPR. -/
structure Inputs (K : Type*) where
  α : K
  z : K
  a : K
  b : K
  c : K

/-! ## The label columns (`x^comp`, `x_out^comp`) and witness (`W_comp`) -/

/-- Null subformula-state tag. -/
def nullStateTag : ℕ := 10

/-- The **public label + witness** of one compute row.
    `x^comp = (state, (s, f), e)`; `x_out^comp = (sf1, sf2, sf3)` with each subformula
    `(sf_state_j, (child_subject, child_formula), sf_evaluation)`;
    `W_comp = (ln_prev, ln, mem_record₁, mem_record₂, mem_record₃)`.
    `sf{j}_st` is `none` for ⊥ (null tag) or `some` opcode tag; the default is `none`. -/
structure Pub (K : Type*) where
  state : State
  s : FP K                           -- input_subject
  f : FP K                           -- input_formula
  e : FP K                           -- evaluation
  sf1_st : Option K := none          -- subformula 1 state tag (`none` ↔ nullStateTag)
  sf1_s : FP K                       -- subformula 1: child subject / formula / evaluation
  sf1_f : FP K
  sf1_e : FP K
  sf2_st : Option K := none
  sf2_s : FP K                       -- subformula 2
  sf2_f : FP K
  sf2_e : FP K
  sf3_st : Option K := none
  sf3_s : FP K                       -- subformula 3
  sf3_f : FP K
  sf3_e : FP K
  ln_prev : K                        -- ln(i−1)
  ln : K                             -- ln(i)
  mr1 : MemRec K                     -- the three memory records
  mr2 : MemRec K
  mr3 : MemRec K
  /-- Form R `C'` carried on the compute row.  `none` means `1`. -/
  certC? : Option K := none

/-- Row `C'`.  Unset rows stay at `1`, the `λ = 1`, `c = 0` value. -/
def Pub.certC (p : Pub K) : K := p.certC?.getD 1

/-! ## Authoritative external-memory requests -/

/-- The raw external-memory requests emitted by one compute row, in canonical slot order
    `mr1`, `mr2`, `mr3`.  Padding records are omitted exactly when they equal `MemRec.zero`.
    Encoding into the IO record coordinates is not done here. -/
@[reducible] noncomputable def requestRecords (pub : Pub K)
    (decNonzero : (r : MemRec K) → Decidable (r ≠ (MemRec.zero : MemRec K)) :=
      fun _ => Classical.propDecidable _) : List (MemRec K) :=
  [pub.mr1, pub.mr2, pub.mr3].filter
    (fun r => @decide (r ≠ (MemRec.zero : MemRec K)) (decNonzero r))

/-- `requestRecords` is the filter of the three memory records by `≠ MemRec.zero`, with the default decidability instance. -/
@[simp]
theorem requestRecords_spec (pub : Pub K) :
    requestRecords pub =
      [pub.mr1, pub.mr2, pub.mr3].filter
        (fun r => decide (r ≠ (MemRec.zero : MemRec K))) :=
  by
    unfold requestRecords
    apply congrArg (fun f : MemRec K → Bool => [pub.mr1, pub.mr2, pub.mr3].filter f)
    funext r
    apply congrArg (fun d : Decidable (r ≠ (MemRec.zero : MemRec K)) => @decide _ d)
    exact Subsingleton.elim _ _

/-- Exact nonzero-filter behavior: a record occurs in a row's external requests precisely when it
    is nonzero and occurs in one of the three request slots.  Slot order and multiplicity are fixed
    by `requestRecords_spec`. -/
theorem mem_requestRecords_iff (pub : Pub K) (r : MemRec K) :
    r ∈ requestRecords pub ↔
      r ≠ (MemRec.zero : MemRec K) ∧
        (r = pub.mr1 ∨ r = pub.mr2 ∨ r = pub.mr3) := by
  simp [requestRecords, and_comm]

/-- The **formula-decomposition columns**: head/tail chain of the formula.
    `f_t = mr1.child`, `f_th = mr2.child`, `f_tth = mr3.child` are recoverable from `W`; `f_h`
    (the formula head) is the one genuinely-extra column, the unique `cons`-preimage. -/
structure Dec (K : Type*) where
  f_h : FP K
  f_t : FP K
  f_th : FP K
  f_tt : FP K
  f_tth : FP K
  f_ttt : FP K

/-- The **auxiliary gate columns**: `cons_inv` and `inv_gen`. -/
structure Extra (K : Type*) where
  consInv : K
  invGen  : K

/-! ## Generalized-inverse / gate algebra lemmas

    These are the field-arithmetic cores of the non-linear gates. -/

section Gates
variable {F : Type*} [Field F]

/-- Existence of a (right) inverse witnesses non-vanishing: `∃ w, x·w = 1 ↔ x ≠ 0`. -/
theorem exists_inv_iff (x : F) : (∃ w : F, x * w = 1) ↔ x ≠ 0 := by
  constructor
  · rintro ⟨w, hw⟩ hx; rw [hx, zero_mul] at hw; exact zero_ne_one hw
  · intro hx; exact ⟨x⁻¹, mul_inv_cancel₀ hx⟩

/-- **Opcode-3 gate**.  With `x := z − sf1_e.size` and
    `bb := e.leaf`, the four gates (booleanity of `bb`, `inv_gen` the generalized inverse of `x`,
    and the correlation `inv_gen·x + bb = 1`) are satisfiable iff `bb = ⟦x = 0⟧` (`1` when `x=0`,
    i.e. the subformula is an atom; `0` when a cell). -/
theorem gate3 (x bb : F) :
    (bb * (1 - bb) = 0 ∧ ∃ w : F, w * (w * x - 1) = 0 ∧ x * (w * x - 1) = 0 ∧ w * x + bb = 1)
      ↔ bb = (if x = 0 then 1 else 0) := by
  constructor
  · rintro ⟨-, w, h2, h3, h4⟩
    by_cases hx : x = 0
    · subst hx; rw [if_pos rfl]; linear_combination h4
    · rw [if_neg hx]
      -- from h3: x·(wx−1)=0, x≠0 ⟹ wx−1=0 ⟹ wx=1 ⟹ bb=0
      have hwx : w * x - 1 = 0 := by
        rcases mul_eq_zero.mp h3 with h | h
        · exact absurd h hx
        · exact h
      linear_combination h4 - hwx
  · intro hbb
    by_cases hx : x = 0
    · subst hx
      rw [if_pos rfl] at hbb; subst hbb
      refine ⟨by ring, 0, by ring, by ring, by ring⟩
    · rw [if_neg hx] at hbb; subst hbb
      refine ⟨by ring, x⁻¹, ?_, ?_, ?_⟩
      · rw [inv_mul_cancel₀ hx]; ring
      · rw [inv_mul_cancel₀ hx]; ring
      · rw [inv_mul_cancel₀ hx]; ring

/-- **Opcode-5 gate**.  With differences `d1,d2,d3` of the two
    subformula fingerprints, RLC `L := a·d1 + b·d2 + c·d3`, and `ev := e.leaf`, the five gates
    are satisfiable iff `ev = ⟦(d1,d2,d3) ≠ 0⟧` (`0` when equal, `1` when not), **provided** the
    RLC is non-degenerate on unequal inputs. -/
theorem gate5 (a b c d1 d2 d3 ev : F)
    (hnd : ¬(d1 = 0 ∧ d2 = 0 ∧ d3 = 0) → a * d1 + b * d2 + c * d3 ≠ 0) :
    (ev * (1 - ev) = 0 ∧ (1 - ev) * d1 = 0 ∧ (1 - ev) * d2 = 0 ∧ (1 - ev) * d3 = 0 ∧
        ∃ w : F, w * (a * d1 + b * d2 + c * d3 + (1 - ev)) = 1)
      ↔ ev = (if (d1 = 0 ∧ d2 = 0 ∧ d3 = 0) then 0 else 1) := by
  constructor
  · rintro ⟨hb, h1, h2, h3, w, h5⟩
    by_cases heq : d1 = 0 ∧ d2 = 0 ∧ d3 = 0
    · rw [if_pos heq]
      obtain ⟨e1, e2, e3⟩ := heq
      rcases mul_eq_zero.mp hb with h | h
      · exact h
      · -- 1 − ev = 0 ⟹ ev = 1; but then w·0 = 1, contradiction
        exfalso
        have hev : ev = 1 := by linear_combination -h
        rw [hev, e1, e2, e3] at h5; simp at h5
    · rw [if_neg heq]
      rcases mul_eq_zero.mp hb with h | h
      · -- ev = 0 forces d = 0, contradicting heq
        exfalso; subst h
        simp only [sub_zero, one_mul] at h1 h2 h3
        exact heq ⟨h1, h2, h3⟩
      · linear_combination -h
  · intro hev
    by_cases heq : d1 = 0 ∧ d2 = 0 ∧ d3 = 0
    · rw [if_pos heq] at hev; subst hev
      obtain ⟨e1, e2, e3⟩ := heq
      refine ⟨by ring, by rw [e1]; ring, by rw [e2]; ring, by rw [e3]; ring, 1, ?_⟩
      rw [e1, e2, e3]; ring
    · rw [if_neg heq] at hev; subst hev
      have hL : a * d1 + b * d2 + c * d3 ≠ 0 := hnd heq
      refine ⟨by ring, by ring, by ring, by ring, (a * d1 + b * d2 + c * d3)⁻¹, ?_⟩
      rw [show a * d1 + b * d2 + c * d3 + (1 - 1) = a * d1 + b * d2 + c * d3 by ring]
      exact inv_mul_cancel₀ hL

/-- **Opcode-6 branch selection**.  For a boolean selector
    `sel ∈ {0,1}`, the arithmetic branch `(1−sel)·x + sel·y` equals the `if`-branch. -/
theorem branch_select (sel x y : F) (hsel : sel = 0 ∨ sel = 1) :
    (1 - sel) * x + sel * y = (if sel = 0 then x else y) := by
  rcases hsel with h | h <;> subst h <;> simp

/-- **Opcode-8/11 product-inverse gate**.
    `∃ w, p·q·w = 1 ↔ (p ≠ 0 ∧ q ≠ 0)` — the constraint is satisfiable iff both sizes are
    nonzero. -/
theorem gate_prod (p q : F) : (∃ w : F, p * q * w = 1) ↔ (p ≠ 0 ∧ q ≠ 0) := by
  rw [exists_inv_iff, mul_ne_zero_iff]

end Gates

/-! ### Bridge lemmas relating gate outputs to the honest operations `qm`, `eqOp`, booleanity -/

/-- The OP_3 gate output `⟦z − x.size = 0⟧` is exactly `qm z x` (Nock `?`). -/
theorem qm_eq (z : K) (x : FP K) :
    (if z - x.size = 0 then (1 : K) else 0) = FP.qm z x := by
  unfold FP.qm
  by_cases h : x.size = z
  · rw [if_pos (by rw [h]; ring), if_pos h]
  · rw [if_neg (by rw [sub_eq_zero]; exact fun hh => h hh.symm), if_neg h]

/-- The OP_5 gate output `⟦x = y⟧` (as componentwise differences) is exactly `eqOp x y`. -/
theorem eqOp_eq (x y : FP K) :
    (if (x.size - y.size = 0 ∧ x.dyck - y.dyck = 0 ∧ x.leaf - y.leaf = 0) then (0 : K) else 1)
      = FP.eqOp x y := by
  unfold FP.eqOp
  by_cases h : x = y
  · subst h; rw [if_pos ⟨sub_self _, sub_self _, sub_self _⟩, if_pos rfl]
  · rw [if_neg, if_neg h]
    rintro ⟨h1, h2, h3⟩
    exact h (FP.ext (by linear_combination h1) (by linear_combination h2)
      (by linear_combination h3))

/-- Booleanity in product form vs set form (EC.6.1 etc.). -/
theorem bool_iff (x : K) : x * (1 - x) = 0 ↔ (x = 0 ∨ x = 1) := by
  constructor
  · intro h; rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination -h)
  · rintro (h | h) <;> subst h <;> ring

/-! ## State selectors and the State-Variables block -/

/-- One-hot encoding of a state. -/
def opSel (st : State) : State → K := fun s => if s = st then 1 else 0

/-- `Σ_{j=0}^{9} g j` over the ten numeric opcodes. -/
def sum09 (g : State → K) : K :=
  g State.s0 + g State.s1 + g State.s2 + g State.s3 + g State.s4 + g State.s5
    + g State.s6 + g State.s7 + g State.s8 + g State.s9

/-- `Σ_{j=0}^{9} j · g j`. -/
def sumJ (g : State → K) : K :=
  (0 : K) * g State.s0 + (1 : K) * g State.s1 + (2 : K) * g State.s2 + (3 : K) * g State.s3
    + (4 : K) * g State.s4 + (5 : K) * g State.s5 + (6 : K) * g State.s6 + (7 : K) * g State.s7
    + (8 : K) * g State.s8 + (9 : K) * g State.s9

/-- **State-Variables constraints**, with `op := opSel pub.state`.
    SV1 is the type declaration; SV2 booleanity, SV3 one-hot, SV4–6 tie `f_h` to the opcode. -/
def SVsat (inp : Inputs K) (pub : Pub K) (dec : Dec K) (consInv : K) : Prop :=
  let op : State → K := opSel pub.state
  (∀ j : State, op j * (1 - op j) = 0) ∧                                       -- SV2
  (op State.cons + sum09 op = 1) ∧                                             -- SV3
  ((1 - op State.cons) * dec.f_h.size = inp.z * sum09 op) ∧                     -- SV4
  ((1 - op State.cons) * dec.f_h.dyck
      + op State.cons * (1 - dec.f_h.dyck * consInv) = 0) ∧                     -- SV5
  ((1 - op State.cons) * dec.f_h.leaf = sumJ op)                                -- SV6

/-- SV2 (booleanity) holds for every one-hot vector. -/
theorem opSel_boolean (st : State) : ∀ j, opSel (K := K) st j * (1 - opSel st j) = 0 := by
  intro j; simp only [opSel]; by_cases h : j = st <;> simp [h]

/-- SV3 (one-hot sum) holds for every one-hot vector. -/
theorem opSel_oneHot (st : State) : opSel st State.cons + sum09 (opSel (K := K) st) = (1 : K) := by
  cases st <;> simp [opSel, sum09]

def headAtom (dec : Dec K) (z k : K) : Prop :=
  dec.f_h.size = z ∧ dec.f_h.dyck = 0 ∧ dec.f_h.leaf = k

def headCell (dec : Dec K) : Prop := dec.f_h.dyck ≠ 0

def SVhead (inp : Inputs K) (pub : Pub K) (dec : Dec K) : Prop :=
  if pub.state = State.cons then headCell dec
  else headAtom dec inp.z (pub.state.toNat : K)

/-! ### Reduced values of the selector sums (used to discharge SV4–6). -/

@[simp] theorem opcons_val (st : State) :
    opSel st State.cons = if st = State.cons then (1 : K) else 0 := by
  cases st <;> simp [opSel]

@[simp] theorem sum09_val (st : State) :
    sum09 (opSel st) = if st = State.cons then (0 : K) else 1 := by
  cases st <;> simp [sum09, opSel]

@[simp] theorem sumJ_val (st : State) :
    sumJ (opSel st) = if st = State.cons then (0 : K) else (st.toNat : K) := by
  cases st <;> simp [sumJ, opSel, State.toNat]

/-- **`(∃ cons_inv, SVsat) ↔ SVhead`.**  The State-Variables block is satisfiable iff the
    formula head has the shape dictated by the opcode. -/
theorem SV_head_iff (inp : Inputs K) (pub : Pub K) (dec : Dec K) :
    (∃ c, SVsat inp pub dec c) ↔ SVhead inp pub dec := by
  simp only [SVsat, SVhead, headAtom, headCell, opcons_val, sum09_val, sumJ_val]
  by_cases hc : pub.state = State.cons
  · simp only [if_pos hc]
    constructor
    · rintro ⟨c, -, -, -, h5, -⟩
      intro hd; rw [hd] at h5; simp at h5
    · intro hc2
      refine ⟨(dec.f_h.dyck)⁻¹, opSel_boolean _, ?_, ?_, ?_, ?_⟩
      · norm_num
      · ring
      · rw [mul_inv_cancel₀ hc2]; ring
      · ring
  · simp only [if_neg hc]
    constructor
    · rintro ⟨c, -, -, h4, h5, h6⟩
      exact ⟨by linear_combination h4, by linear_combination h5, by linear_combination h6⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨0, opSel_boolean _, ?_, ?_, ?_, ?_⟩
      · norm_num
      · rw [h1]; ring
      · rw [h2]; ring
      · rw [h3]; ring

/-! ### Adversarial selector pinning:  a FREE one-hot selector is forced to `opSel s`

  `SVsat`/`RAPcomp` hardcode the selector at the honest value `op := opSel pub.state`.  A real
  AIR prover supplies the eleven selector columns `op_0 … op_9, op_cons` FREELY.  This block
  proves that the State-Variable gates leave no adversarial freedom: SV2 (booleanity) + SV3
  (one-hot sum) force `op = opSel s` for a *unique* state `s`, and SV4–6 then pin `s`'s
  formula-head shape to `f_h` (via `SV_head_iff`).  This is the lemma cited as `SV_pins_head`
  in the file docstring and used by `AIR.computeAIR_sound_free`.

  FIELD SUBTLETY.  "Booleanity + sum = 1 ⟹ one-hot" is FALSE in small characteristic: e.g. in
  characteristic 2, three ones sum to `1`.  The honest counting argument (`op` boolean ⟹ its
  sum equals the cardinality of its support, which must then cast to `1`) needs the support
  cardinality (`≤ 11`) to be recoverable from its image in `K`.  We take exactly that as the
  hypothesis `hchar : ∀ n ≤ 11, (n : K) = 1 → n = 1` (satisfied by every field of
  characteristic `0` or `> 11`, in particular the Goldilocks field and its extension). -/

/-- `State` is a `Fintype` (the eleven opcodes), used to count the support of a free selector. -/
instance : Fintype State :=
  ⟨⟨[State.s0, State.s1, State.s2, State.s3, State.s4, State.s5, State.s6, State.s7,
      State.s8, State.s9, State.cons], by decide⟩,
   by intro x; cases x <;> decide⟩

/-- The eleven-term selector sum as a `Finset.univ` sum. -/
theorem sum_univ_eq (g : State → K) : (∑ j : State, g j) = g State.cons + sum09 g := by
  have h : (∑ j : State, g j)
    = g State.s0 + (g State.s1 + (g State.s2 + (g State.s3 + (g State.s4 + (g State.s5
      + (g State.s6 + (g State.s7 + (g State.s8 + (g State.s9 + (g State.cons + 0)))))))))) := rfl
  rw [h]; simp only [sum09]; ring

/-- **One-hot from booleanity + sum = 1.**  A selector `op` with every entry in `{0,1}` (SV2)
    whose eleven entries sum to `1` (SV3) is forced to be a one-hot `opSel s`.  Needs `hchar`
    (see the field-subtlety note): the support cardinality (`≤ 11`) casts to `1`, so it is `1`. -/
theorem oneHot_of_bool_sum (op : State → K)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hb : ∀ j, op j = 0 ∨ op j = 1)
    (hsum : op State.cons + sum09 op = 1) :
    ∃ s, op = opSel s := by
  classical
  set S := Finset.univ.filter (fun j => op j = 1) with hS
  have hcast : (S.card : K) = op State.cons + sum09 op := by
    rw [← sum_univ_eq]
    have hcong : (∑ j : State, op j) = ∑ j : State, (if op j = 1 then (1 : K) else 0) :=
      Finset.sum_congr rfl (fun j _ => by rcases hb j with h | h <;> simp [h])
    rw [hcong, Finset.sum_boole]
  rw [hsum] at hcast
  have hle : S.card ≤ 11 := by
    have := Finset.card_filter_le (Finset.univ : Finset State) (fun j => op j = 1)
    rwa [Finset.card_univ, (by decide : Fintype.card State = 11)] at this
  have hc1 : S.card = 1 := hchar S.card hle hcast
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc1
  refine ⟨a, funext fun j => ?_⟩
  simp only [opSel]
  by_cases hja : j = a
  · subst hja
    have haS : j ∈ S := by rw [ha]; exact Finset.mem_singleton_self j
    have : op j = 1 := (Finset.mem_filter.mp haS).2
    simp [this]
  · have hnotin : j ∉ S := by rw [ha, Finset.mem_singleton]; exact hja
    have hne : op j ≠ 1 := fun hc => hnotin (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hc⟩)
    rcases hb j with h | h
    · simp [hja, h]
    · exact absurd h hne

/-- **State-Variables block over a FREE selector `op`**.  Identical
    to `SVsat` but with `op` an explicit free argument rather than `opSel pub.state`. -/
def SVsatFree (inp : Inputs K) (op : State → K) (dec : Dec K) (consInv : K) : Prop :=
  (∀ j : State, op j * (1 - op j) = 0) ∧                                        -- SV2
  (op State.cons + sum09 op = 1) ∧                                             -- SV3
  ((1 - op State.cons) * dec.f_h.size = inp.z * sum09 op) ∧                     -- SV4
  ((1 - op State.cons) * dec.f_h.dyck
      + op State.cons * (1 - dec.f_h.dyck * consInv) = 0) ∧                     -- SV5
  ((1 - op State.cons) * dec.f_h.leaf = sumJ op)                                -- SV6

/-- `SVsat` is exactly `SVsatFree` at the honest one-hot selector (`rfl`). -/
theorem SVsat_eq_free (inp : Inputs K) (pub : Pub K) (dec : Dec K) (c : K) :
    SVsat inp pub dec c = SVsatFree inp (opSel pub.state) dec c := rfl

/-- **`SV_pins_head`.**  Over a FREE selector `op`, the full State-Variables block
    `SVsatFree` forces `op = opSel s` for a unique state `s` (via `oneHot_of_bool_sum`), and then
    SV4–6 pin the formula head `f_h` to `s`'s shape (`SVhead`, via `SV_head_iff`): an atom
    `(z, 0, s.toNat)` for `OP_k`, a cell (`dyck ≠ 0`) for `cons`.  So no adversarial assignment of
    the free selector columns satisfies the SV gates except the honest one-hot dictated by `f_h`.
    (`pub` supplies only the ambient row; the conclusion is about `{pub with state := s}`.) -/
theorem SV_pins_head (inp : Inputs K) (op : State → K) (pub : Pub K) (dec : Dec K) (consInv : K)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (h : SVsatFree inp op dec consInv) :
    ∃ s : State, op = opSel s ∧ SVhead inp { pub with state := s } dec := by
  obtain ⟨s, hs⟩ := oneHot_of_bool_sum op hchar (fun j => (bool_iff (op j)).mp (h.1 j)) h.2.1
  refine ⟨s, hs, ?_⟩
  have hsv : SVsat inp { pub with state := s } dec consInv := by
    rw [SVsat_eq_free, ← hs]; exact h
  exact (SV_head_iff inp { pub with state := s } dec).mp ⟨consInv, hsv⟩

/-! ## Memory-record block, evaluation blocks, and the RAP / algorithmic verifier -/

/-- Subformula-slot zero constraints. -/
def sfz1 (pub : Pub K) : Prop := pub.sf1_s = 0 ∧ pub.sf1_f = 0 ∧ pub.sf1_e = 0
def sfz2 (pub : Pub K) : Prop := pub.sf2_s = 0 ∧ pub.sf2_f = 0 ∧ pub.sf2_e = 0
def sfz3 (pub : Pub K) : Prop := pub.sf3_s = 0 ∧ pub.sf3_f = 0 ∧ pub.sf3_e = 0

/-- **Memory Record Accesses**, records 2 and 3 and the `ln` recurrence,
    per state.  (Record 1 is the always-operative constraint; see `RAPcomp`.)  Shared verbatim
    between `RAPcomp` and `Vcomp` — the algorithm's
    memory checks and the constraint-spec memory subsection.  `ln` for `cons` uses `α^1`
    (`cons ≠ OP_0`, the head is a cell), so `op_11` is included in the recurrence. -/
def memBlk (inp : Inputs K) (pub : Pub K) (dec : Dec K) : Prop :=
  match pub.state with
  | .s0 =>
      pub.mr2 = ⟨pub.s, pub.e, dec.f_t.leaf, pub.ln_prev * inp.α ^ 2⟩ ∧ pub.mr3 = MemRec.zero
        ∧ pub.ln = pub.ln_prev * inp.α ^ 2 ∧ dec.f_t.size = inp.z ∧ dec.f_t.dyck = 0
  | .s1 | .s3 | .s4 | .cons =>
      pub.mr2 = MemRec.zero ∧ pub.mr3 = MemRec.zero ∧ pub.ln = pub.ln_prev * inp.α
  | .s2 | .s5 | .s7 | .s8 =>
      pub.mr2 = ⟨dec.f_t, dec.f_th, 2, pub.ln_prev * inp.α ^ 2⟩
        ∧ FP.cons inp.z dec.f_th dec.f_tt = dec.f_t ∧ pub.mr3 = MemRec.zero
        ∧ pub.ln = pub.ln_prev * inp.α ^ 2
  | .s6 =>
      pub.mr2 = ⟨dec.f_t, dec.f_th, 2, pub.ln_prev * inp.α ^ 2⟩
        ∧ FP.cons inp.z dec.f_th dec.f_tt = dec.f_t
        ∧ pub.mr3 = ⟨dec.f_tt, dec.f_tth, 2, pub.ln_prev * inp.α ^ 3⟩
        ∧ FP.cons inp.z dec.f_tth dec.f_ttt = dec.f_tt ∧ pub.ln = pub.ln_prev * inp.α ^ 3
  | .s9 =>
      pub.mr2 = ⟨dec.f_t, dec.f_th, 2, pub.ln_prev * inp.α ^ 2⟩
        ∧ FP.cons inp.z dec.f_th dec.f_tt = dec.f_t
        ∧ pub.mr3 = ⟨pub.sf1_e, pub.sf2_f, dec.f_th.leaf, pub.ln_prev * inp.α ^ 3⟩
        ∧ pub.ln = pub.ln_prev * inp.α ^ 3

/-- **RAP evaluation block**, using the shared inverse column `g = inv_gen`. -/
def evalR (inp : Inputs K) (pub : Pub K) (dec : Dec K) (g : K) : Prop :=
  match pub.state with
  | .s0 => sfz1 pub ∧ sfz2 pub ∧ sfz3 pub
  | .s1 => pub.e = dec.f_t ∧ sfz1 pub ∧ sfz2 pub ∧ sfz3 pub
  | .s2 => pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_th ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_tt
        ∧ pub.sf3_s = pub.sf1_e ∧ pub.sf3_f = pub.sf2_e ∧ pub.e = pub.sf3_e
  | .s3 => pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_t ∧ sfz2 pub ∧ sfz3 pub
        ∧ pub.e.size = inp.z ∧ pub.e.dyck = 0
        ∧ pub.e.leaf * (1 - pub.e.leaf) = 0
        ∧ g * (g * (inp.z - pub.sf1_e.size) - 1) = 0
        ∧ (inp.z - pub.sf1_e.size) * (g * (inp.z - pub.sf1_e.size) - 1) = 0
        ∧ g * (inp.z - pub.sf1_e.size) + pub.e.leaf = 1
  | .s4 => pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_t ∧ pub.sf1_e.size = inp.z ∧ pub.sf1_e.dyck = 0
        ∧ sfz2 pub ∧ sfz3 pub ∧ pub.e = FP.inc inp.z pub.sf1_e
  | .s5 => pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_th ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_tt
        ∧ sfz3 pub ∧ pub.e.size = inp.z ∧ pub.e.dyck = 0
        ∧ pub.e.leaf * (1 - pub.e.leaf) = 0
        ∧ (1 - pub.e.leaf) * (pub.sf1_e.size - pub.sf2_e.size) = 0
        ∧ (1 - pub.e.leaf) * (pub.sf1_e.dyck - pub.sf2_e.dyck) = 0
        ∧ (1 - pub.e.leaf) * (pub.sf1_e.leaf - pub.sf2_e.leaf) = 0
        ∧ g * (inp.a * (pub.sf1_e.size - pub.sf2_e.size) + inp.b * (pub.sf1_e.dyck - pub.sf2_e.dyck)
              + inp.c * (pub.sf1_e.leaf - pub.sf2_e.leaf) + (1 - pub.e.leaf)) = 1
  | .s6 => pub.sf1_s = pub.s
        ∧ pub.sf1_f = FP.add (FP.smul (1 - pub.sf2_e.leaf) dec.f_tth)
                             (FP.smul pub.sf2_e.leaf dec.f_ttt)
        ∧ pub.e = pub.sf1_e ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_th
        ∧ pub.sf2_e.size = inp.z ∧ pub.sf2_e.dyck = 0
        ∧ pub.sf2_e.leaf * (1 - pub.sf2_e.leaf) = 0 ∧ sfz3 pub
  | .s7 => pub.sf1_s = pub.sf2_e ∧ pub.sf1_f = dec.f_tt ∧ pub.e = pub.sf1_e
        ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_th ∧ sfz3 pub
  | .s8 => pub.sf1_s = FP.cons inp.z pub.sf2_e pub.s ∧ pub.sf1_f = dec.f_tt ∧ pub.e = pub.sf1_e
        ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_th ∧ sfz3 pub
        ∧ pub.sf2_e.size * pub.s.size * g = 1
  | .s9 => pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_tt ∧ pub.sf2_s = pub.sf1_e
        ∧ pub.e = pub.sf2_e ∧ sfz3 pub
        ∧ dec.f_th.size = inp.z ∧ dec.f_th.dyck = 0
  | .cons => pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_h ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_t
        ∧ pub.e = FP.cons inp.z pub.sf1_e pub.sf2_e ∧ sfz3 pub
        ∧ pub.sf1_e.size * pub.sf2_e.size * g = 1

/-- **Algorithmic-verifier evaluation block**: the
    honest per-opcode checks, using `qm` (`?`), `inc` (`+`), `eqOp` (`=`), and `cons`. -/
def evalV (inp : Inputs K) (pub : Pub K) (dec : Dec K) : Prop :=
  match pub.state with
  | .s0 => sfz1 pub ∧ sfz2 pub ∧ sfz3 pub
  | .s1 => pub.e = dec.f_t ∧ sfz1 pub ∧ sfz2 pub ∧ sfz3 pub
  | .s2 => pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_th ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_tt
        ∧ pub.sf3_s = pub.sf1_e ∧ pub.sf3_f = pub.sf2_e ∧ pub.e = pub.sf3_e
  | .s3 => pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_t ∧ sfz2 pub ∧ sfz3 pub
        ∧ pub.e.size = inp.z ∧ pub.e.dyck = 0 ∧ pub.e.leaf = FP.qm inp.z pub.sf1_e
  | .s4 => pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_t ∧ pub.sf1_e.size = inp.z ∧ pub.sf1_e.dyck = 0
        ∧ sfz2 pub ∧ sfz3 pub ∧ pub.e = FP.inc inp.z pub.sf1_e
  | .s5 => pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_th ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_tt
        ∧ sfz3 pub ∧ pub.e.size = inp.z ∧ pub.e.dyck = 0 ∧ pub.e.leaf = FP.eqOp pub.sf1_e pub.sf2_e
  | .s6 => pub.sf1_s = pub.s
        ∧ pub.sf1_f = (if pub.sf2_e.leaf = 0 then dec.f_tth else dec.f_ttt)
        ∧ pub.e = pub.sf1_e ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_th
        ∧ pub.sf2_e.size = inp.z ∧ pub.sf2_e.dyck = 0
        ∧ (pub.sf2_e.leaf = 0 ∨ pub.sf2_e.leaf = 1) ∧ sfz3 pub
  | .s7 => pub.sf1_s = pub.sf2_e ∧ pub.sf1_f = dec.f_tt ∧ pub.e = pub.sf1_e
        ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_th ∧ sfz3 pub
  | .s8 => pub.sf1_s = FP.cons inp.z pub.sf2_e pub.s ∧ pub.sf1_f = dec.f_tt ∧ pub.e = pub.sf1_e
        ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_th ∧ sfz3 pub
  | .s9 => pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_tt ∧ pub.sf2_s = pub.sf1_e
        ∧ pub.e = pub.sf2_e ∧ sfz3 pub
        ∧ dec.f_th.size = inp.z ∧ dec.f_th.dyck = 0
  | .cons => pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_h ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_t
        ∧ pub.e = FP.cons inp.z pub.sf1_e pub.sf2_e ∧ sfz3 pub

/-- **The compute RAP `RAP_comp`**: the full degree-tracked constraint
    conjunction for one row, over the auxiliary gate columns `ex = (cons_inv, inv_gen)`. -/
def RAPcomp (inp : Inputs K) (pub : Pub K) (dec : Dec K) (ex : Extra K) : Prop :=
  pub.f = FP.cons inp.z dec.f_h dec.f_t
    ∧ pub.mr1 = ⟨pub.f, dec.f_t, 3, pub.ln_prev * inp.α⟩
    ∧ SVsat inp pub dec ex.consInv
    ∧ memBlk inp pub dec
    ∧ evalR inp pub dec ex.invGen

/-- **The algorithmic verifier `V_comp`**. -/
def Vcomp (inp : Inputs K) (pub : Pub K) (dec : Dec K) : Prop :=
  pub.f = FP.cons inp.z dec.f_h dec.f_t
    ∧ pub.mr1 = ⟨pub.f, dec.f_t, 3, pub.ln_prev * inp.α⟩
    ∧ SVhead inp pub dec
    ∧ memBlk inp pub dec
    ∧ evalV inp pub dec

/-- In state `s9`, `Vcomp` forces `f_th` to be an atom fingerprint: `size = z` and `dyck = 0`. -/
theorem Vcomp.s9_axis_atom_shape {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hstate : pub.state = .s9) (h : Vcomp inp pub dec) :
    dec.f_th.size = inp.z ∧ dec.f_th.dyck = 0 := by
  obtain ⟨_, _, _, _, heval⟩ := h
  simp only [evalV, hstate] at heval
  obtain ⟨_, _, _, _, _, hsize, hdyck⟩ := heval
  exact ⟨hsize, hdyck⟩

/-- **Well-formedness** — the paper's implicit genericity/nonzero conditions that make the exact
    biconditional hold: random `(a,b,c)` make the OP_5 RLC injective on
    unequal inputs; sizes are nonzero powers of `z ≠ 0` (OP_8 / OP_11). -/
structure WF (inp : Inputs K) (pub : Pub K) : Prop where
  rlc5 : pub.state = State.s5 → pub.sf1_e ≠ pub.sf2_e →
    inp.a * (pub.sf1_e.size - pub.sf2_e.size) + inp.b * (pub.sf1_e.dyck - pub.sf2_e.dyck)
      + inp.c * (pub.sf1_e.leaf - pub.sf2_e.leaf) ≠ 0
  size8 : pub.state = State.s8 → pub.sf2_e.size ≠ 0 ∧ pub.s.size ≠ 0
  size11 : pub.state = State.cons → pub.sf1_e.size ≠ 0 ∧ pub.sf2_e.size ≠ 0

/-- Branch-selection on fingerprints: for `sel ∈ {0,1}` the arithmetic branch is the `if`. -/
theorem FP_branch_eq (sel : K) (x y : FP K) (h : sel = 0 ∨ sel = 1) :
    FP.add (FP.smul (1 - sel) x) (FP.smul sel y) = if sel = 0 then x else y := by
  rcases h with h | h <;> subst h
  · rw [if_pos rfl]; ext <;> simp [FP.add, FP.smul]
  · rw [if_neg (by norm_num)]; ext <;> simp [FP.add, FP.smul]

/-- **`(∃ inv_gen, evalR) ↔ evalV`** — the evaluation constraints are satisfiable iff the
    algorithm's per-opcode checks pass.  Gate states use `gate3`/`gate5`/`gate_prod`. -/
theorem eval_iff (inp : Inputs K) (pub : Pub K) (dec : Dec K) (wf : WF inp pub) :
    (∃ g, evalR inp pub dec g) ↔ evalV inp pub dec := by
  cases hst : pub.state
  -- Non-gate opcodes: `evalR` does not use `inv_gen`, so `(∃ g, P) ↔ P`.
  case s0 => simp only [evalR, evalV, hst]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩
  case s1 => simp only [evalR, evalV, hst]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩
  case s2 => simp only [evalR, evalV, hst]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩
  case s4 => simp only [evalR, evalV, hst]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩
  case s7 => simp only [evalR, evalV, hst]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩
  case s9 => simp only [evalR, evalV, hst]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩
  -- OP_3: `?` via the generalized inverse (EC.3, gate3 + qm_eq).
  case s3 =>
    simp only [evalR, evalV, hst]
    constructor
    · rintro ⟨g, h1, h2, h3, h4, h5, h6, hb, hg1, hg2, hg3⟩
      refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
      rw [← qm_eq]
      exact (gate3 (inp.z - pub.sf1_e.size) pub.e.leaf).mp ⟨hb, g, hg1, hg2, hg3⟩
    · rintro ⟨h1, h2, h3, h4, h5, h6, hqm⟩
      obtain ⟨hb, w, hg1, hg2, hg3⟩ :=
        (gate3 (inp.z - pub.sf1_e.size) pub.e.leaf).mpr (by rw [qm_eq]; exact hqm)
      exact ⟨w, h1, h2, h3, h4, h5, h6, hb, hg1, hg2, hg3⟩
  -- OP_5: `=` via the RLC generalized inverse (EC.5, gate5 + eqOp_eq); needs `wf.rlc5`.
  case s5 =>
    simp only [evalR, evalV, hst]
    have hnd : ¬(pub.sf1_e.size - pub.sf2_e.size = 0 ∧ pub.sf1_e.dyck - pub.sf2_e.dyck = 0
        ∧ pub.sf1_e.leaf - pub.sf2_e.leaf = 0) →
        inp.a * (pub.sf1_e.size - pub.sf2_e.size) + inp.b * (pub.sf1_e.dyck - pub.sf2_e.dyck)
          + inp.c * (pub.sf1_e.leaf - pub.sf2_e.leaf) ≠ 0 := by
      intro hnd0
      apply wf.rlc5 hst
      intro heq
      exact hnd0 ⟨by rw [heq]; ring, by rw [heq]; ring, by rw [heq]; ring⟩
    constructor
    · rintro ⟨g, h1, h2, h3, h4, h5, h6, h7, hb, hd1, hd2, hd3, hg5⟩
      refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_⟩
      rw [← eqOp_eq]
      exact (gate5 inp.a inp.b inp.c _ _ _ pub.e.leaf hnd).mp ⟨hb, hd1, hd2, hd3, g, hg5⟩
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7, hqm⟩
      obtain ⟨hb, hd1, hd2, hd3, w, hg5⟩ :=
        (gate5 inp.a inp.b inp.c _ _ _ pub.e.leaf hnd).mpr (by rw [eqOp_eq]; exact hqm)
      exact ⟨w, h1, h2, h3, h4, h5, h6, h7, hb, hd1, hd2, hd3, hg5⟩
  -- OP_6: branch selection under booleanity (branch_select / FP_branch_eq + bool_iff).
  case s6 =>
    simp only [evalR, evalV, hst]
    constructor
    · rintro ⟨g, h1, hf, h3, h4, h5, h6, h7, hbool, hsfz⟩
      have hsel := (bool_iff pub.sf2_e.leaf).mp hbool
      exact ⟨h1, by rw [hf]; exact FP_branch_eq _ _ _ hsel, h3, h4, h5, h6, h7, hsel, hsfz⟩
    · rintro ⟨h1, hf, h3, h4, h5, h6, h7, hsel, hsfz⟩
      exact ⟨0, h1, by rw [hf]; exact (FP_branch_eq _ _ _ hsel).symm, h3, h4, h5, h6, h7,
        (bool_iff pub.sf2_e.leaf).mpr hsel, hsfz⟩
  -- OP_8: cons implicitly checks sizes ≠ 0 (EC.8.1, gate_prod); needs `wf.size8`.
  case s8 =>
    simp only [evalR, evalV, hst]
    obtain ⟨hs2, hs⟩ := wf.size8 hst
    constructor
    · rintro ⟨g, h1, h2, h3, h4, h5, h6, _⟩; exact ⟨h1, h2, h3, h4, h5, h6⟩
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      exact ⟨(pub.sf2_e.size * pub.s.size)⁻¹, h1, h2, h3, h4, h5, h6,
        mul_inv_cancel₀ (mul_ne_zero hs2 hs)⟩
  -- OP_11 / cons: cons implicitly checks sizes ≠ 0 (EC.11.1, gate_prod); needs `wf.size11`.
  case cons =>
    simp only [evalR, evalV, hst]
    obtain ⟨h1s, h2s⟩ := wf.size11 hst
    constructor
    · rintro ⟨g, h1, h2, h3, h4, h5, h6, _⟩; exact ⟨h1, h2, h3, h4, h5, h6⟩
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      exact ⟨(pub.sf1_e.size * pub.sf2_e.size)⁻¹, h1, h2, h3, h4, h5, h6,
        mul_inv_cancel₀ (mul_ne_zero h1s h2s)⟩

/-- **`Lem:equiv_compute`.**  `RAP_comp` admits a satisfying assignment for
    `(x^comp, x_out^comp, W_comp)` (over the auxiliary columns `cons_inv`, `inv_gen`) iff the
    algorithmic verifier `V_comp` accepts. -/
theorem equiv_compute (inp : Inputs K) (pub : Pub K) (dec : Dec K) (wf : WF inp pub) :
    (∃ ex : Extra K, RAPcomp inp pub dec ex) ↔ Vcomp inp pub dec := by
  unfold RAPcomp Vcomp
  constructor
  · rintro ⟨ex, hal, hmr1, hsv, hmem, hev⟩
    exact ⟨hal, hmr1, (SV_head_iff inp pub dec).mp ⟨ex.consInv, hsv⟩, hmem,
      (eval_iff inp pub dec wf).mp ⟨ex.invGen, hev⟩⟩
  · rintro ⟨hal, hmr1, hsh, hmem, hvr⟩
    obtain ⟨c, hsv⟩ := (SV_head_iff inp pub dec).mpr hsh
    obtain ⟨g, hev⟩ := (eval_iff inp pub dec wf).mpr hvr
    exact ⟨⟨c, g⟩, hal, hmr1, hsv, hmem, hev⟩

/-! ═══════════════════════════════════════════════════════════════════════════════════════════
  ## Combined single-gate optimization
  ═══════════════════════════════════════════════════════════════════════════════════════════

  The paper notes that "one can reduce the total number of gates by combining
  SOME of these constraints into one" and DISPLAYS a single FOLDED gate: the
  one-hot-selector-weighted sum of the four non-linear "`= 1`" gates — EC.3.4,
  EC.5.5, EC.8.1, EC.11.1 — set equal to `1`.

  We define this folded expression `combinedGate` over the eleven FREE selector columns `op` and
  prove (`combinedGate_opSel`) that UNDER the one-hot selector `op = opSel st` it COLLAPSES to
  exactly the selected opcode's `= 1`-gate LHS (and to `0` for the seven opcodes that have no such
  gate).  Hence the single gate `combinedGate (opSel st) g = 1` is EQUIVALENT to the individual
  `= 1` constraint that already sits as the LAST conjunct of `evalR`'s `s3/s5/s8/cons` branches
  (`combinedGate_s3_iff`, `_s5_iff`, `combinedGate_prod_s8`, `_cons`).  So the fold carries NO
  separate content — it is a pure display reformulation of four gates as one, which is precisely
  the equality proved here (genuine `=`/`↔`, not a weakening).

  Note on the OP_8 term.  The paper's combined display writes
  the OP_8 term as `op_8 · sf2_e.size · inv_gen`, OMITTING the `input_subject.size` factor present
  in the individual gate EC.8.1: `sf2_e.size · input_subject.size · inv_gen = 1`.  We fold
  the ACTUAL gate EC.8.1 (WITH `input_subject.size`), matching `evalR`'s `s8` branch — folding the
  displayed 2-factor term would DROP a constraint (a weakening).  The omission in the display
  is a transcription slip in the paper's illustrative example. -/

/-- The **folded single gate** `Σ_{k∈{3,5,8,11}} op_k · G_k`, where each `G_k`
    is the LHS of the corresponding non-linear "`= 1`" gate in `evalR`, and `op` is the free
    selector-column vector, `g = inv_gen` the shared generalized-inverse column.  The OP_8 term
    carries `input_subject.size` per EC.8.1 (see the note on the OP_8 term in the section header). -/
def combinedGate (inp : Inputs K) (pub : Pub K) (op : State → K) (g : K) : K :=
  op State.s3 * (g * (inp.z - pub.sf1_e.size) + pub.e.leaf)                       -- EC.3.4
    + op State.s5 * (g * (inp.a * (pub.sf1_e.size - pub.sf2_e.size)
        + inp.b * (pub.sf1_e.dyck - pub.sf2_e.dyck)
        + inp.c * (pub.sf1_e.leaf - pub.sf2_e.leaf) + (1 - pub.e.leaf)))          -- EC.5.5
    + op State.s8 * (pub.sf2_e.size * pub.s.size * g)                             -- EC.8.1
    + op State.cons * (pub.sf1_e.size * pub.sf2_e.size * g)                       -- EC.11.1

/-- **One-hot collapse.**  Under the one-hot selector `op = opSel st`, the
    folded gate equals exactly the selected opcode's `= 1`-gate LHS — and `0` for the opcodes that
    have no such gate.  This is the algebraic content of the fold: the selector-weighted sum keeps
    only the active term. -/
theorem combinedGate_opSel (inp : Inputs K) (pub : Pub K) (g : K) (st : State) :
    combinedGate inp pub (opSel st) g =
      (match st with
       | .s3 => g * (inp.z - pub.sf1_e.size) + pub.e.leaf
       | .s5 => g * (inp.a * (pub.sf1_e.size - pub.sf2_e.size)
           + inp.b * (pub.sf1_e.dyck - pub.sf2_e.dyck)
           + inp.c * (pub.sf1_e.leaf - pub.sf2_e.leaf) + (1 - pub.e.leaf))
       | .s8 => pub.sf2_e.size * pub.s.size * g
       | .cons => pub.sf1_e.size * pub.sf2_e.size * g
       | _ => 0) := by
  cases st <;> simp only [combinedGate, opSel, reduceCtorEq, ↓reduceIte] <;> ring

/-- **OP_3.**  The folded gate `= 1` is exactly EC.3.4 — the last conjunct of
    `evalR`'s `s3` branch and the `= 1` core of `gate3`. -/
theorem combinedGate_s3_iff (inp : Inputs K) (pub : Pub K) (g : K) :
    combinedGate inp pub (opSel State.s3) g = 1
      ↔ g * (inp.z - pub.sf1_e.size) + pub.e.leaf = 1 := by
  rw [combinedGate_opSel]

/-- **OP_5.**  The folded gate `= 1` is exactly EC.5.5 — the last conjunct of
    `evalR`'s `s5` branch and the `= 1` core of `gate5`. -/
theorem combinedGate_s5_iff (inp : Inputs K) (pub : Pub K) (g : K) :
    combinedGate inp pub (opSel State.s5) g = 1
      ↔ g * (inp.a * (pub.sf1_e.size - pub.sf2_e.size)
          + inp.b * (pub.sf1_e.dyck - pub.sf2_e.dyck)
          + inp.c * (pub.sf1_e.leaf - pub.sf2_e.leaf) + (1 - pub.e.leaf)) = 1 := by
  rw [combinedGate_opSel]

/-- **OP_8 (full `gate_prod`).**  Existentially closing the shared inverse column, the folded gate
    `= 1` for `op = opSel s8` is exactly `gate_prod` on the two sizes: it is
    satisfiable iff `sf2_e.size ≠ 0 ∧ input_subject.size ≠ 0`.  (WITH the `input_subject.size`
    factor — see the note on the OP_8 term.) -/
theorem combinedGate_prod_s8 (inp : Inputs K) (pub : Pub K) :
    (∃ g, combinedGate inp pub (opSel State.s8) g = 1)
      ↔ (pub.sf2_e.size ≠ 0 ∧ pub.s.size ≠ 0) := by
  simp only [combinedGate_opSel]; exact gate_prod pub.sf2_e.size pub.s.size

/-- **OP_11 / cons (full `gate_prod`).**  Likewise for `op = opSel cons`: the folded gate `= 1` is
    exactly `gate_prod` on the two subformula-evaluation sizes. -/
theorem combinedGate_prod_cons (inp : Inputs K) (pub : Pub K) :
    (∃ g, combinedGate inp pub (opSel State.cons) g = 1)
      ↔ (pub.sf1_e.size ≠ 0 ∧ pub.sf2_e.size ≠ 0) := by
  simp only [combinedGate_opSel]; exact gate_prod pub.sf1_e.size pub.sf2_e.size

/-- **No content for the other opcodes.**  For any `st ∉ {s3, s5, s8, cons}` the folded gate
    vanishes identically (`= 0`), so the single combined gate `= 1` is simply NOT among these
    opcodes' constraints — consistent with the paper folding only "SOME" gates. -/
theorem combinedGate_other (inp : Inputs K) (pub : Pub K) (g : K) (st : State)
    (h : st ≠ State.s3 ∧ st ≠ State.s5 ∧ st ≠ State.s8 ∧ st ≠ State.cons) :
    combinedGate inp pub (opSel st) g = 0 := by
  obtain ⟨h3, h5, h8, hc⟩ := h
  cases st <;> first
    | (exact absurd rfl h3) | (exact absurd rfl h5) | (exact absurd rfl h8)
    | (exact absurd rfl hc)
    | (rw [combinedGate_opSel])

/-! ═══════════════════════════════════════════════════════════════════════════════════════════
  ## The language `L_comp` as a literal set
  ═══════════════════════════════════════════════════════════════════════════════════════════

  The paper defines the compute transition-function language as the SET:
    `L_comp = { (x^comp, x_out^comp) ∈ LT_comp × (LT_comp ∪ {⊥})³ | ∃ W, V_comp((x,x_out),W) = 0 }`
  and, in the appendix, as this set UNIONED with the fully-padded terminal `{⊥}⁴`.
  We build this set object LITERALLY on top of the algorithmic verifier `Vcomp`.

  * `LTcomp = OP × ((N^λ, N^λ), N^λ)` is the compute label: an opcode `st` with
    the `(input_subject, input_formula)` and `evaluation` fingerprints.
  * `LT_comp ∪ {⊥}` is `Option (LTcomp K)` (`none = ⊥`); the OUTPUT space `(LT_comp ∪ {⊥})³` is
    `OutComp = (Option (LTcomp K))³` — the three subformula slots, each either
    a full label or `⊥`.
  * Arithmetization convention `⊥ ↦ (0,0,0)` for fingerprints and
    `⊥ ↦ nullStateTag` (= 10) for subformula state tags (`Pub.sf*_st = none`).
  * `V_comp((x,x_out),W) = 0` is `Vcomp inp pub dec`; SET membership existentially closes the
    paper's witness `W_comp = (ln_prev, ln, mem_record₁₋₃)` together with the
    auxiliary decomposition columns `dec`. -/

/-- The compute label `LT_comp = OP × ((N^λ, N^λ), N^λ)`: opcode `st`, the input
    subject/formula fingerprints, and the evaluation fingerprint. -/
structure LTcomp (K : Type*) where
  st      : State
  subj    : FP K
  formula : FP K
  eval    : FP K

/-- The compute OUTPUT space `(LT_comp ∪ {⊥})³`: three subformula slots, each a full label or `⊥` (`none`). -/
abbrev OutComp (K : Type*) := Option (LTcomp K) × Option (LTcomp K) × Option (LTcomp K)

/-- One output slot `LT_comp ∪ {⊥}` as its `(subject, formula, evaluation)` fingerprints, with the
    arithmetization convention `⊥ = none ↦ (0,0,0)`. -/
def slotFP (o : Option (LTcomp K)) : FP K × FP K × FP K :=
  match o with
  | none => (0, 0, 0)
  | some l => (l.subj, l.formula, l.eval)

/-- Subformula state tag as ℕ: `nullStateTag` when ⊥, else the paper opcode tag. -/
def slotStateTagNat (o : Option (LTcomp K)) : ℕ :=
  match o with
  | none => nullStateTag
  | some l =>
      match l.st with
      | .s0 => 0 | .s1 => 1 | .s2 => 2 | .s3 => 3 | .s4 => 4
      | .s5 => 5 | .s6 => 6 | .s7 => 7 | .s8 => 8 | .s9 => 9 | .cons => 11

/-- Subformula state as `Option K` for `Pub.sf*_st` (`none` ↔ null). -/
def slotStateTagOpt (o : Option (LTcomp K)) : Option K :=
  match o with
  | none => none
  | some l => some (slotStateTagNat (some l) : K)

/-- Field element for an `sf*_st` slot (`none` ↦ `nullStateTag`). -/
def sfStateVal [Field K] (st : Option K) : K :=
  st.getD (nullStateTag : K)

/-- Reconstruct the row `Pub` from an input label `x`, an output triple `xout`, and the paper's
    witness `W_comp = (ln_prev, ln, mem_record₁₋₃)`.  Subformula slots use `slotFP`
    and `slotStateTagOpt`. -/
def toPub (x : LTcomp K) (xout : OutComp K)
    (ln_prev ln : K) (mr1 mr2 mr3 : MemRec K) : Pub K where
  state := x.st
  s := x.subj
  f := x.formula
  e := x.eval
  sf1_st := slotStateTagOpt xout.1
  sf1_s := (slotFP xout.1).1
  sf1_f := (slotFP xout.1).2.1
  sf1_e := (slotFP xout.1).2.2
  sf2_st := slotStateTagOpt xout.2.1
  sf2_s := (slotFP xout.2.1).1
  sf2_f := (slotFP xout.2.1).2.1
  sf2_e := (slotFP xout.2.1).2.2
  sf3_st := slotStateTagOpt xout.2.2
  sf3_s := (slotFP xout.2.2).1
  sf3_f := (slotFP xout.2.2).2.1
  sf3_e := (slotFP xout.2.2).2.2
  ln_prev := ln_prev
  ln := ln
  mr1 := mr1
  mr2 := mr2
  mr3 := mr3

/-- **`L_comp`.**  The compute transition-function language as a literal set:
    `{ (x, x_out) ∈ LT_comp × (LT_comp ∪ {⊥})³ | ∃ W_comp, V_comp((x,x_out), W_comp) = 0 }`, with
    `V_comp(...) = 0` given by `Vcomp` and the witness `W_comp` (and the auxiliary decomposition
    columns) existentially quantified. -/
def Lcomp (inp : Inputs K) : Set (LTcomp K × OutComp K) :=
  { p | ∃ (ln_prev ln : K) (mr1 mr2 mr3 : MemRec K) (dec : Dec K),
      Vcomp inp (toPub p.1 p.2 ln_prev ln mr1 mr2 mr3) dec }

/-- **`L_comp`.**  The main-body set `Lcomp`, embedded via
    `x ↦ some x`, UNIONED with the fully-padded terminal `{⊥}⁴` (input `⊥` and all three outputs
    `⊥`) — the paper's `∪ {⊥}⁴`. -/
def LcompApp (inp : Inputs K) : Set (Option (LTcomp K) × OutComp K) :=
  { p | ∃ x, p.1 = some x ∧ (x, p.2) ∈ Lcomp inp } ∪ { (none, none, none, none) }

/-- **`L_comp` is nonempty (content witness).** -/
theorem Lcomp_nonempty (inp : Inputs K) : (Lcomp inp).Nonempty := by
  classical
  refine ⟨(⟨State.s0, 0, FP.cons inp.z (FP.atomFP inp.z 0) (FP.atomFP inp.z 0), 0⟩,
            (none, none, none)), 0, 0 * inp.α ^ 2,
          ⟨FP.cons inp.z (FP.atomFP inp.z 0) (FP.atomFP inp.z 0), FP.atomFP inp.z 0, 3, 0 * inp.α⟩,
          ⟨0, 0, 0, 0 * inp.α ^ 2⟩, MemRec.zero,
          ⟨FP.atomFP inp.z 0, FP.atomFP inp.z 0, 0, 0, 0, 0⟩, ?_⟩
  refine ⟨rfl, rfl, ⟨rfl, rfl, ?_⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩,
          ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩⟩
  exact Nat.cast_zero.symm

end ComputeTable
end Nock
