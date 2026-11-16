/-
  Nock/Jet/Interp.lean

ONE straight-line interpreter over J-2's `Tpl` / `Ex` / `ev`:

  * one row per node.  The canonical node numbering `nodesOf T` is PRE-ORDER over the body
    (the body root is node `0`, the output row), followed by one block per argument `i`: a `var`
    node (the argument's export read) and the argument's SHAPE GUARD nodes (`tlN n` / `isNil` /
    `nth j` / `isF`), which replace the compiled formula's Nock guard;
  * `var` / `nth` / `tlN` / `pair` (= `build`) are export READS: their value is fixed by a memory
    record, used as a black box (`ReadsGenuine`: the record is genuine);
  * `add` / `mul` are ONE degree-2 gate over the two looked-up operand values; `const`, `isF`,
    `isNil` are local checks on the row's own cells;
  * the operand values `x`, `y` of a row are LOOKED UP by node id inside the call
    (`NodeLookupSound`: a functional map `look : ℕ → Noun`, per call, that serves every row's own
    value and every operand consume — the hypothesis standing for the lookup balance).

  No Schwartz–Zippel identity, no `β`, no fingerprint reads.  At table level the values are nouns
  (in the chip: handles of nouns / field elements).

  Theorems: `interp_sound` (constraints + `NodeLookupSound` + `ReadsGenuine` ⇒ the output row's value
  is `T.sem p s`, hence `HoldsN ⟨s, compile p T, ·⟩` by J-2's `compile_rel_iff_holdsN`),
  `interp_complete` (the honest table satisfies every constraint and outputs `T.sem p s`),
  `nodesOf_length` (row count), and the matmul instance (`n = 2` honest table + one tampered row).
-/
import Nock.Jet.AutogenMatmul

set_option autoImplicit false

namespace Nock.Jet.Interp

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen

/-! ## §1 Rows, tables, constraints -/

/-- The row operations.  `var i ax`: argument `i` read at subject axis `ax`. -/
inductive JOp where
  | var (i ax : ℕ)
  | const (c : ℕ)
  | add
  | mul
  | pair
  | nth (j : ℕ)
  | tlN (n : ℕ)
  | isF
  | isNil
  deriving DecidableEq, Repr

/-- Number of looked-up operands. -/
def JOp.arity : JOp → ℕ
  | .add | .mul | .pair => 2
  | .nth _ | .tlN _ | .isF | .isNil => 1
  | .var _ _ | .const _ => 0

/-- A node of the canonical numbering: id, op, operand node ids (`0` when unused). -/
structure JNode where
  id : ℕ
  op : JOp
  a : ℕ
  b : ℕ
  deriving DecidableEq, Repr

/-- **A row of the J table**: the node (id, op, operand ids), the call id, the node's value and the
two looked-up operand values. -/
structure JRow where
  node : JNode
  call : ℕ
  val : Noun
  x : Noun
  y : Noun
  deriving DecidableEq, Repr

abbrev JTable := List JRow

/-- The rows of one call. -/
def callRows (t : JTable) (c : ℕ) : List JRow := t.filter fun r => r.call == c

/-- Genuine structural reads (a memory record, as a partial function). -/
def tailO : ℕ → Noun → Option Noun
  | 0, v => some v
  | _ + 1, .atom _ => none
  | j + 1, .cell _ t => tailO j t

def hdO : Noun → Option Noun
  | .cell h _ => some h
  | .atom _ => none

def nthO (j : ℕ) (v : Noun) : Option Noun := (tailO j v).bind hdO

def isFieldAtom (p : ℕ) : Noun → Bool
  | .atom v => decide (v < p)
  | .cell _ _ => false

/-- **The per-row local constraints** (value `v`, operands `x y`): `add`/`mul` is the degree-2 gate. -/
def localOK (p : ℕ) : JOp → Noun → Noun → Noun → Bool
  | .const c, v, _, _ => decide (v = .atom c)
  | .add, v, x, y => decide (v = .atom ((atomVal x + atomVal y) % p))
  | .mul, v, x, y => decide (v = .atom ((atomVal x * atomVal y) % p))
  | .isF, v, x, _ => isFieldAtom p x && decide (v = x)
  | .isNil, v, x, _ => decide (x = .atom 0) && decide (v = x)
  | _, _, _, _ => true

/-- **The export-read relation**: what a genuine memory record asserts for a read row. -/
def readOK (s : Noun) : JOp → Noun → Noun → Noun → Bool
  | .var _ ax, v, _, _ => decide (Noun.slot ax s = some v)
  | .nth j, v, x, _ => decide (nthO j x = some v)
  | .tlN n, v, x, _ => decide (tailO n x = some v)
  | .pair, v, x, y => decide (v = .cell x y)
  | _, _, _, _ => true

def LocalOK (p : ℕ) (r : JRow) : Prop := localOK p r.node.op r.val r.x r.y = true

/-- **`ReadsGenuine`** (black box: J-1's / memory's "records are genuine") for the call's
subject `s`. -/
def ReadsGenuine (s : Noun) (rows : List JRow) : Prop :=
  ∀ r ∈ rows, readOK s r.node.op r.val r.x r.y = true

/-- **`NodeLookupSound`** (the hypothesis standing for the in-chip node-value lookup balance): one
functional map from node id to value, per call, serving each row's own value (provide) and each
used operand (consume). -/
def NodeLookupSound (rows : List JRow) : Prop :=
  ∃ look : ℕ → Noun, (∀ r ∈ rows, look r.node.id = r.val) ∧
    ∀ r ∈ rows, (0 < r.node.op.arity → r.x = look r.node.a) ∧
      (1 < r.node.op.arity → r.y = look r.node.b)

/-! ## §2 The canonical node numbering -/

def exSz {k : ℕ} : Ex k → ℕ
  | .var _ => 1
  | .const _ => 1
  | .add e₁ e₂ => exSz e₁ + exSz e₂ + 1
  | .mul e₁ e₂ => exSz e₁ + exSz e₂ + 1
  | .pair e₁ e₂ => exSz e₁ + exSz e₂ + 1
  | .nth _ e => exSz e + 1

/-- Body nodes, pre-order from base id `b` (the root gets `b`). -/
def exNodes {k : ℕ} (ax : Fin k → ℕ) : ℕ → Ex k → List JNode
  | b, .var i => [⟨b, .var i.val (ax i), 0, 0⟩]
  | b, .const c => [⟨b, .const c, 0, 0⟩]
  | b, .add e₁ e₂ =>
      ⟨b, .add, b + 1, b + 1 + exSz e₁⟩ :: (exNodes ax (b + 1) e₁ ++ exNodes ax (b + 1 + exSz e₁) e₂)
  | b, .mul e₁ e₂ =>
      ⟨b, .mul, b + 1, b + 1 + exSz e₁⟩ :: (exNodes ax (b + 1) e₁ ++ exNodes ax (b + 1 + exSz e₁) e₂)
  | b, .pair e₁ e₂ =>
      ⟨b, .pair, b + 1, b + 1 + exSz e₁⟩ :: (exNodes ax (b + 1) e₁ ++ exNodes ax (b + 1 + exSz e₁) e₂)
  | b, .nth j e => ⟨b, .nth j, b + 1, 0⟩ :: exNodes ax (b + 1) e

def gSz : Ty → ℕ
  | .F => 1
  | .L n τ => 2 + n * (1 + gSz τ)
  | .N => 0

/-- Guard nodes of a list's elements `js` (operand `r` = the list's node). -/
def gElems (g : ℕ → ℕ → List JNode) (sz r : ℕ) : ℕ → List ℕ → List JNode
  | _, [] => []
  | b, j :: js => ⟨b, .nth j, r, 0⟩ :: (g (b + 1) b ++ gElems g sz r (b + 1 + sz) js)

/-- Shape-guard nodes of type `τ` for the noun at node `r`, from base id `b`. -/
def gNodes : Ty → ℕ → ℕ → List JNode
  | .F, b, r => [⟨b, .isF, r, 0⟩]
  | .N, _, _ => []
  | .L n τ, b, r =>
      ⟨b, .tlN n, r, 0⟩ :: ⟨b + 1, .isNil, b, 0⟩ :: gElems (gNodes τ) (gSz τ) r (b + 2) (List.range n)

/-- Argument blocks: the `var` read and its guard. -/
def inNodes (T : Tpl) : ℕ → List (Fin T.k) → List JNode
  | _, [] => []
  | b, i :: is =>
      ⟨b, .var i.val (T.ax i), 0, 0⟩ :: (gNodes (T.inTy i) (b + 1) b ++ inNodes T (b + 1 + gSz (T.inTy i)) is)

def inSz (T : Tpl) (is : List (Fin T.k)) : ℕ := (is.map fun i => 1 + gSz (T.inTy i)).sum

/-- **`nodesOf T`**: the canonical node numbering (body pre-order, root `0`, then the arguments). -/
def nodesOf (T : Tpl) : List JNode :=
  exNodes T.ax 0 T.body ++ inNodes T (exSz T.body) (List.finRange T.k)

/-! ### Ids are `0, 1, …, N−1` in order -/

theorem rng_app (m : ℕ) : ∀ s n, List.range' s m ++ List.range' (s + m) n = List.range' s (m + n) := by
  induction m with
  | zero => intro s n; simp
  | succ m ih =>
    intro s n
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [List.range', List.cons_append]
    rw [show s + (m + 1) = (s + 1) + m by omega, ih]

theorem exNodes_ids {k : ℕ} (ax : Fin k → ℕ) :
    ∀ (e : Ex k) (b : ℕ), (exNodes ax b e).map JNode.id = List.range' b (exSz e) := by
  intro e
  induction e with
  | var i => intro b; rfl
  | const c => intro b; rfl
  | add e₁ e₂ ih₁ ih₂ =>
    intro b
    simp only [exNodes, exSz, List.map_cons, List.map_append, ih₁, ih₂]
    rw [rng_app]; rfl
  | mul e₁ e₂ ih₁ ih₂ =>
    intro b
    simp only [exNodes, exSz, List.map_cons, List.map_append, ih₁, ih₂]
    rw [rng_app]; rfl
  | pair e₁ e₂ ih₁ ih₂ =>
    intro b
    simp only [exNodes, exSz, List.map_cons, List.map_append, ih₁, ih₂]
    rw [rng_app]; rfl
  | nth j e ih =>
    intro b
    simp only [exNodes, exSz, List.map_cons, ih]; rfl

theorem gNodes_ids : ∀ (τ : Ty) (b r : ℕ), (gNodes τ b r).map JNode.id = List.range' b (gSz τ) := by
  intro τ
  induction τ with
  | F => intro b r; rfl
  | N => intro b r; rfl
  | L n τ ih =>
    intro b r
    have hel : ∀ (js : List ℕ) (b : ℕ), (gElems (gNodes τ) (gSz τ) r b js).map JNode.id =
        List.range' b (js.length * (1 + gSz τ)) := by
      intro js
      induction js with
      | nil => intro b; simp [gElems]
      | cons j js ihj =>
        intro b
        simp only [gElems, List.map_cons, List.map_append, ih, ihj, List.length_cons]
        rw [rng_app, Nat.succ_mul]
        generalize js.length * (1 + gSz τ) = M
        rw [show M + (1 + gSz τ) = (gSz τ + M) + 1 by omega]
        rfl
    simp only [gNodes, gSz, List.map_cons, hel, List.length_range]
    rw [show 2 + n * (1 + gSz τ) = n * (1 + gSz τ) + 1 + 1 by omega]
    rfl

theorem inNodes_ids (T : Tpl) :
    ∀ (is : List (Fin T.k)) (b : ℕ), (inNodes T b is).map JNode.id = List.range' b (inSz T is) := by
  intro is
  induction is with
  | nil => intro b; rfl
  | cons i is ih =>
    intro b
    simp only [inNodes, inSz, List.map_cons, List.map_append, gNodes_ids, List.sum_cons]
    rw [show (List.map (fun i => 1 + gSz (T.inTy i)) is).sum = inSz T is from rfl, ih, rng_app]
    rw [show 1 + gSz (T.inTy i) + inSz T is = (gSz (T.inTy i) + inSz T is) + 1 by omega]
    rfl

theorem nodesOf_ids (T : Tpl) :
    (nodesOf T).map JNode.id = List.range' 0 (exSz T.body + inSz T (List.finRange T.k)) := by
  simp only [nodesOf, List.map_append, exNodes_ids, inNodes_ids]
  have := rng_app (exSz T.body) 0 (inSz T (List.finRange T.k))
  simpa using this

/-- **Row count**: one row per node; body nodes plus, per argument, `1 + gSz (inTy i)`. -/
theorem nodesOf_length (T : Tpl) :
    (nodesOf T).length = exSz T.body + inSz T (List.finRange T.k) := by
  have := congrArg List.length (nodesOf_ids T)
  simpa using this

/-! ## §3 Read lemmas -/

theorem ntail_succ' (j : ℕ) (v : Noun) : ntail (j + 1) v = ntail j (ntl v) := by
  induction j generalizing v with
  | zero => rfl
  | succ j ih => show ntl (ntail (j + 1) v) = ntl (ntail j (ntl v)); rw [ih]

theorem tailO_some {j : ℕ} {v u : Noun} (h : tailO j v = some u) : ntail j v = u := by
  induction j generalizing v with
  | zero => simp [tailO] at h; simp [ntail, h]
  | succ j ih =>
    cases v with
    | atom _ => simp [tailO] at h
    | cell hd t =>
      rw [ntail_succ']
      simp only [tailO] at h
      simpa [ntl] using ih h

theorem nthO_some {j : ℕ} {v w : Noun} (h : nthO j v = some w) : nhd (ntail j v) = w := by
  unfold nthO at h
  cases ht : tailO j v with
  | none => simp [ht] at h
  | some u =>
    simp only [ht, Option.bind_some] at h
    rw [tailO_some ht]
    cases u with
    | atom _ => simp [hdO] at h
    | cell a b => simp [hdO] at h; simp [nhd, h]

theorem shapeL_iff (ok : Noun → Bool) : ∀ (n : ℕ) (v : Noun),
    shapeL ok n v = true ↔
      (∀ j < n, ∃ w, nthO j v = some w ∧ ok w = true) ∧ tailO n v = some (.atom 0) := by
  intro n
  induction n with
  | zero => intro v; simp [shapeL, tailO]
  | succ n ih =>
    intro v
    cases v with
    | atom m => simp [shapeL, tailO]
    | cell h t =>
      simp only [shapeL, Bool.and_eq_true, ih t, tailO]
      constructor
      · rintro ⟨hh, hj, ht⟩
        refine ⟨fun j hj' => ?_, ht⟩
        cases j with
        | zero => exact ⟨h, by simp [nthO, tailO, hdO], hh⟩
        | succ j => simpa [nthO, tailO] using hj j (by omega)
      · rintro ⟨hj, ht⟩
        refine ⟨?_, fun j hj' => ?_, ht⟩
        · obtain ⟨w, hw, hok⟩ := hj 0 (by omega)
          simp [nthO, tailO, hdO] at hw
          subst hw
          exact hok
        · simpa [nthO, tailO] using hj (j + 1) (by omega)

theorem isFieldAtom_eq (p : ℕ) (v : Noun) : isFieldAtom p v = shapeOK p .F v := by
  cases v <;> rfl

/-! ## §4 Soundness -/

/-- A node's constraints read through the lookup map. -/
def NOK (p : ℕ) (s : Noun) (look : ℕ → Noun) (nd : JNode) : Prop :=
  localOK p nd.op (look nd.id) (look nd.a) (look nd.b) = true ∧
    readOK s nd.op (look nd.id) (look nd.a) (look nd.b) = true

theorem nok_of_row {p : ℕ} {s : Noun} {look : ℕ → Noun} {r : JRow} (hl : LocalOK p r)
    (hr : readOK s r.node.op r.val r.x r.y = true) (hv : look r.node.id = r.val)
    (hx : 0 < r.node.op.arity → r.x = look r.node.a) (hy : 1 < r.node.op.arity → r.y = look r.node.b) :
    NOK p s look r.node := by
  obtain ⟨⟨id, op, a, b⟩, c, v, x, y⟩ := r
  simp only [LocalOK] at hl hr hv hx hy ⊢
  subst hv
  cases op <;> simp only [JOp.arity] at hx hy <;>
    first
    | (have hx' := hx (by omega); have hy' := hy (by omega); subst hx' hy'; exact ⟨hl, hr⟩)
    | (have hx' := hx (by omega); subst hx'; exact ⟨by simpa [localOK] using hl, by simpa [readOK] using hr⟩)
    | exact ⟨by simpa [localOK] using hl, by simpa [readOK] using hr⟩

theorem body_sound {p : ℕ} {s : Noun} {look : ℕ → Noun} {k : ℕ} {ax : Fin k → ℕ}
    {a : Fin k → Noun} (hs : ∀ i, Noun.slot (ax i) s = some (a i)) :
    ∀ (e : Ex k) (b : ℕ), (∀ nd ∈ exNodes ax b e, NOK p s look nd) → look b = ev p a e := by
  intro e
  induction e with
  | var i =>
    intro b h
    have h0 := (h ⟨b, .var i.val (ax i), 0, 0⟩ (by simp [exNodes])).2
    simp only [readOK, decide_eq_true_eq, hs i] at h0
    exact (Option.some.inj h0).symm
  | const c =>
    intro b h
    have h0 := (h ⟨b, .const c, 0, 0⟩ (by simp [exNodes])).1
    simpa [localOK, ev] using h0
  | add e₁ e₂ ih₁ ih₂ =>
    intro b h
    have h0 := (h ⟨b, .add, b + 1, b + 1 + exSz e₁⟩ (by simp [exNodes])).1
    have h₁ := ih₁ (b + 1) fun nd hn => h nd (by simp [exNodes, hn])
    have h₂ := ih₂ (b + 1 + exSz e₁) fun nd hn => h nd (by simp [exNodes, hn])
    simp only [localOK, decide_eq_true_eq] at h0
    rw [h0, h₁, h₂]; rfl
  | mul e₁ e₂ ih₁ ih₂ =>
    intro b h
    have h0 := (h ⟨b, .mul, b + 1, b + 1 + exSz e₁⟩ (by simp [exNodes])).1
    have h₁ := ih₁ (b + 1) fun nd hn => h nd (by simp [exNodes, hn])
    have h₂ := ih₂ (b + 1 + exSz e₁) fun nd hn => h nd (by simp [exNodes, hn])
    simp only [localOK, decide_eq_true_eq] at h0
    rw [h0, h₁, h₂]; rfl
  | pair e₁ e₂ ih₁ ih₂ =>
    intro b h
    have h0 := (h ⟨b, .pair, b + 1, b + 1 + exSz e₁⟩ (by simp [exNodes])).2
    have h₁ := ih₁ (b + 1) fun nd hn => h nd (by simp [exNodes, hn])
    have h₂ := ih₂ (b + 1 + exSz e₁) fun nd hn => h nd (by simp [exNodes, hn])
    simp only [readOK, decide_eq_true_eq] at h0
    rw [h0, h₁, h₂]; rfl
  | nth j e ih =>
    intro b h
    have h0 := (h ⟨b, .nth j, b + 1, 0⟩ (by simp [exNodes])).2
    have h₁ := ih (b + 1) fun nd hn => h nd (by simp [exNodes, hn])
    simp only [readOK, decide_eq_true_eq] at h0
    rw [h₁] at h0
    exact (nthO_some h0).symm

theorem guard_sound {p : ℕ} {s : Noun} {look : ℕ → Noun} :
    ∀ (τ : Ty) (b r : ℕ), (∀ nd ∈ gNodes τ b r, NOK p s look nd) → shapeOK p τ (look r) = true := by
  intro τ
  induction τ with
  | F =>
    intro b r h
    have h0 := (h ⟨b, .isF, r, 0⟩ (by simp [gNodes])).1
    simp only [localOK, Bool.and_eq_true] at h0
    rw [← isFieldAtom_eq]; exact h0.1
  | N => intro b r _; rfl
  | L n τ ih =>
    intro b r h
    have ht := (h ⟨b, .tlN n, r, 0⟩ (by simp [gNodes])).2
    have hz := (h ⟨b + 1, .isNil, b, 0⟩ (by simp [gNodes])).1
    simp only [readOK, decide_eq_true_eq] at ht
    simp only [localOK, Bool.and_eq_true, decide_eq_true_eq] at hz
    have hel : ∀ (js : List ℕ) (b' : ℕ), (∀ nd ∈ gElems (gNodes τ) (gSz τ) r b' js, NOK p s look nd) →
        ∀ j ∈ js, ∃ w, nthO j (look r) = some w ∧ shapeOK p τ w = true := by
      intro js
      induction js with
      | nil => intro b' _ j hj; simp at hj
      | cons j js ihj =>
        intro b' h' j' hj'
        rcases List.mem_cons.1 hj' with rfl | hj'
        · have h0 := (h' ⟨b', .nth j', r, 0⟩ (by simp [gElems])).2
          simp only [readOK, decide_eq_true_eq] at h0
          exact ⟨_, h0, ih (b' + 1) b' fun nd hn => h' nd (by simp [gElems, hn])⟩
        · exact ihj (b' + 1 + gSz τ) (fun nd hn => h' nd (by simp [gElems, hn])) j' hj'
    have he := hel (List.range n) (b + 2) fun nd hn => h nd (by simp [gNodes, hn])
    rw [shapeOK_L, shapeL_iff]
    exact ⟨fun j hj => he j (List.mem_range.2 hj), by rw [ht, hz.1]⟩

theorem in_sound (T : Tpl) {p : ℕ} {s : Noun} {look : ℕ → Noun} :
    ∀ (is : List (Fin T.k)) (b : ℕ), (∀ nd ∈ inNodes T b is, NOK p s look nd) →
      ∀ i ∈ is, ∃ v, Noun.slot (T.ax i) s = some v ∧ shapeOK p (T.inTy i) v = true := by
  intro is
  induction is with
  | nil => intro b _ i hi; simp at hi
  | cons i is ih =>
    intro b h i' hi'
    rcases List.mem_cons.1 hi' with rfl | hi'
    · have h0 := (h ⟨b, .var i'.val (T.ax i'), 0, 0⟩ (by simp [inNodes])).2
      simp only [readOK, decide_eq_true_eq] at h0
      exact ⟨_, h0, guard_sound (T.inTy i') (b + 1) b fun nd hn => h nd (by simp [inNodes, hn])⟩
    · exact ih (b + 1 + gSz (T.inTy i)) (fun nd hn => h nd (by simp [inNodes, hn])) i' hi'

/-- **`interp_sound`: the jet table's rows for one call are sound for the template.**
For a well-typed template `T` over a positive modulus `p`, a subject `s` and a call `c` of the jet table `t`:
if the rows of call `c` carry the canonical node skeleton of `T`, satisfy every local constraint, are served by
a functional node-value lookup (`NodeLookupSound`) and their export reads are genuine for `s` (`ReadsGenuine`),
then the output row (node `0`) holds a value `v` with `T.sem p s = some v`, and `HoldsN ⟨s, compile p T, v⟩`. -/
theorem interp_sound {p : ℕ} (hp : 0 < p) (T : Tpl) (hT : T.WellTyped p) (s : Noun) (t : JTable)
    (c : ℕ) (hsk : (callRows t c).map JRow.node = nodesOf T)
    (hloc : ∀ r ∈ callRows t c, LocalOK p r) (hlk : NodeLookupSound (callRows t c))
    (hrd : ReadsGenuine s (callRows t c)) (out : JRow) (hout : out ∈ callRows t c)
    (hid : out.node.id = 0) :
    T.sem p s = some out.val ∧ HoldsN ⟨s, compile p T, out.val⟩ := by
  obtain ⟨look, hv, hx⟩ := hlk
  have hN : ∀ nd ∈ nodesOf T, NOK p s look nd := by
    intro nd hnd
    rw [← hsk] at hnd
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hnd
    exact nok_of_row (hloc r hr) (hrd r hr) (hv r hr) (hx r hr).1 (hx r hr).2
  have hin := in_sound T (List.finRange T.k) (exSz T.body)
    (fun nd h => hN nd (List.mem_append_right _ h))
  choose a ha using fun i => hin i (List.mem_finRange i)
  have hbody := body_sound (p := p) (look := look) (ax := T.ax) (fun i => (ha i).1) T.body 0
    (fun nd h => hN nd (List.mem_append_left _ h))
  have hsem : T.sem p s = some out.val :=
    sem_eq_some_iff.2 ⟨a, fun i => (ha i).1, fun i => (ha i).2, by rw [← hv out hout, hid, hbody]⟩
  exact ⟨hsem, (compile_rel_iff_holdsN hp T hT s _).1 hsem⟩

/-! ## §5 Completeness: the honest table -/

def z0 : Noun := .atom 0

def exRows {k : ℕ} (p : ℕ) (ax : Fin k → ℕ) (a : Fin k → Noun) (c : ℕ) : ℕ → Ex k → List JRow
  | b, .var i => [⟨⟨b, .var i.val (ax i), 0, 0⟩, c, a i, z0, z0⟩]
  | b, .const n => [⟨⟨b, .const n, 0, 0⟩, c, .atom n, z0, z0⟩]
  | b, .add e₁ e₂ =>
      ⟨⟨b, .add, b + 1, b + 1 + exSz e₁⟩, c, ev p a (.add e₁ e₂), ev p a e₁, ev p a e₂⟩ ::
        (exRows p ax a c (b + 1) e₁ ++ exRows p ax a c (b + 1 + exSz e₁) e₂)
  | b, .mul e₁ e₂ =>
      ⟨⟨b, .mul, b + 1, b + 1 + exSz e₁⟩, c, ev p a (.mul e₁ e₂), ev p a e₁, ev p a e₂⟩ ::
        (exRows p ax a c (b + 1) e₁ ++ exRows p ax a c (b + 1 + exSz e₁) e₂)
  | b, .pair e₁ e₂ =>
      ⟨⟨b, .pair, b + 1, b + 1 + exSz e₁⟩, c, ev p a (.pair e₁ e₂), ev p a e₁, ev p a e₂⟩ ::
        (exRows p ax a c (b + 1) e₁ ++ exRows p ax a c (b + 1 + exSz e₁) e₂)
  | b, .nth j e =>
      ⟨⟨b, .nth j, b + 1, 0⟩, c, ev p a (.nth j e), ev p a e, z0⟩ :: exRows p ax a c (b + 1) e

def gElemsR (g : ℕ → ℕ → Noun → List JRow) (sz r : ℕ) (v : Noun) (c : ℕ) :
    ℕ → List ℕ → List JRow
  | _, [] => []
  | b, j :: js => ⟨⟨b, .nth j, r, 0⟩, c, nhd (ntail j v), v, z0⟩ ::
      (g (b + 1) b (nhd (ntail j v)) ++ gElemsR g sz r v c (b + 1 + sz) js)

def gRows (c : ℕ) : Ty → ℕ → ℕ → Noun → List JRow
  | .F, b, r, v => [⟨⟨b, .isF, r, 0⟩, c, v, v, z0⟩]
  | .N, _, _, _ => []
  | .L n τ, b, r, v =>
      ⟨⟨b, .tlN n, r, 0⟩, c, ntail n v, v, z0⟩ :: ⟨⟨b + 1, .isNil, b, 0⟩, c, ntail n v, ntail n v, z0⟩ ::
        gElemsR (gRows c τ) (gSz τ) r v c (b + 2) (List.range n)

def inRows (T : Tpl) (a : Fin T.k → Noun) (c : ℕ) : ℕ → List (Fin T.k) → List JRow
  | _, [] => []
  | b, i :: is => ⟨⟨b, .var i.val (T.ax i), 0, 0⟩, c, a i, z0, z0⟩ ::
      (gRows c (T.inTy i) (b + 1) b (a i) ++ inRows T a c (b + 1 + gSz (T.inTy i)) is)

/-- The honest arguments read from the subject (default `0` off the domain). -/
def argsD (T : Tpl) (s : Noun) (i : Fin T.k) : Noun := (Noun.slot (T.ax i) s).getD z0

/-- **The honest table of `T` on `s`** (call id `c`). -/
def honestRows (p : ℕ) (T : Tpl) (s : Noun) (c : ℕ) : List JRow :=
  exRows p T.ax (argsD T s) c 0 T.body ++ inRows T (argsD T s) c (exSz T.body) (List.finRange T.k)

/-! ### Skeleton -/

theorem exRows_nodes {p k : ℕ} (ax : Fin k → ℕ) (a : Fin k → Noun) (c : ℕ) :
    ∀ (e : Ex k) (b : ℕ), (exRows p ax a c b e).map JRow.node = exNodes ax b e := by
  intro e
  induction e with
  | var i => intro b; rfl
  | const n => intro b; rfl
  | add e₁ e₂ ih₁ ih₂ => intro b; simp [exRows, exNodes, ih₁, ih₂]
  | mul e₁ e₂ ih₁ ih₂ => intro b; simp [exRows, exNodes, ih₁, ih₂]
  | pair e₁ e₂ ih₁ ih₂ => intro b; simp [exRows, exNodes, ih₁, ih₂]
  | nth j e ih => intro b; simp [exRows, exNodes, ih]

theorem gRows_nodes (c : ℕ) : ∀ (τ : Ty) (b r : ℕ) (v : Noun),
    (gRows c τ b r v).map JRow.node = gNodes τ b r := by
  intro τ
  induction τ with
  | F => intro b r v; rfl
  | N => intro b r v; rfl
  | L n τ ih =>
    intro b r v
    have hel : ∀ (js : List ℕ) (b : ℕ),
        (gElemsR (gRows c τ) (gSz τ) r v c b js).map JRow.node = gElems (gNodes τ) (gSz τ) r b js := by
      intro js
      induction js with
      | nil => intro b; rfl
      | cons j js ihj => intro b; simp [gElemsR, gElems, ih, ihj]
    simp [gRows, gNodes, hel]

theorem inRows_nodes (T : Tpl) (a : Fin T.k → Noun) (c : ℕ) :
    ∀ (is : List (Fin T.k)) (b : ℕ), (inRows T a c b is).map JRow.node = inNodes T b is := by
  intro is
  induction is with
  | nil => intro b; rfl
  | cons i is ih => intro b; simp [inRows, inNodes, gRows_nodes, ih]

theorem honestRows_nodes (p : ℕ) (T : Tpl) (s : Noun) (c : ℕ) :
    (honestRows p T s c).map JRow.node = nodesOf T := by
  simp [honestRows, nodesOf, exRows_nodes, inRows_nodes]

/-! ### Call ids, local constraints, genuine reads -/

/-- Everything a single honest row must satisfy. -/
def RowGood (p : ℕ) (s : Noun) (c : ℕ) (r : JRow) : Prop :=
  r.call = c ∧ LocalOK p r ∧ readOK s r.node.op r.val r.x r.y = true

theorem exRows_good {p : ℕ} (hp : 0 < p) {k : ℕ} {ax : Fin k → ℕ} {inTy : Fin k → Ty} {s : Noun}
    {a : Fin k → Noun} (hs : ∀ i, Noun.slot (ax i) s = some (a i))
    (ha : ∀ i, shapeOK p (inTy i) (a i) = true) (c : ℕ) {e : Ex k} {τ : Ty}
    (h : HasTy p inTy e τ) : ∀ b, ∀ r ∈ exRows p ax a c b e, RowGood p s c r := by
  induction h with
  | var i =>
    intro b r hr
    simp only [exRows, List.mem_singleton] at hr; subst hr
    exact ⟨rfl, by simp [LocalOK, localOK], by simp [readOK, hs i]⟩
  | const _ =>
    intro b r hr
    simp only [exRows, List.mem_singleton] at hr; subst hr
    exact ⟨rfl, by simp [LocalOK, localOK], by simp [readOK]⟩
  | nil _ =>
    intro b r hr
    simp only [exRows, List.mem_singleton] at hr; subst hr
    exact ⟨rfl, by simp [LocalOK, localOK], by simp [readOK]⟩
  | weakN _ ih => exact ih
  | add _ _ ih₁ ih₂ =>
    intro b r hr
    simp only [exRows, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | hr | hr
    · exact ⟨rfl, by simp [LocalOK, localOK, ev], by simp [readOK]⟩
    · exact ih₁ _ r hr
    · exact ih₂ _ r hr
  | mul _ _ ih₁ ih₂ =>
    intro b r hr
    simp only [exRows, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | hr | hr
    · exact ⟨rfl, by simp [LocalOK, localOK, ev], by simp [readOK]⟩
    · exact ih₁ _ r hr
    · exact ih₂ _ r hr
  | pair _ _ ih₁ ih₂ =>
    intro b r hr
    simp only [exRows, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | hr | hr
    · exact ⟨rfl, by simp [LocalOK, localOK], by simp [readOK, ev]⟩
    · exact ih₁ _ r hr
    · exact ih₂ _ r hr
  | @nth j n τ' e he hj ih =>
    intro b r hr
    simp only [exRows, List.mem_cons] at hr
    rcases hr with rfl | hr
    · have hsh := (ev_spec (ax := ax) hp hs ha he).2
      rw [shapeOK_L, shapeL_iff] at hsh
      obtain ⟨w, hw, -⟩ := hsh.1 j hj
      refine ⟨rfl, by simp [LocalOK, localOK], ?_⟩
      simp only [readOK, ev]
      simp [nthO_some hw]
      exact hw
    · exact ih _ r hr

theorem gRows_good {p : ℕ} {s : Noun} (c : ℕ) : ∀ (τ : Ty) (b r : ℕ) (v : Noun),
    shapeOK p τ v = true → ∀ row ∈ gRows c τ b r v, RowGood p s c row := by
  intro τ
  induction τ with
  | F =>
    intro b r v hv row hrow
    simp only [gRows, List.mem_singleton] at hrow; subst hrow
    refine ⟨rfl, ?_, by simp [readOK]⟩
    simp only [LocalOK, localOK, Bool.and_eq_true, decide_eq_true_eq, and_true]
    rw [isFieldAtom_eq]; exact hv
  | N => intro b r v _ row hrow; simp [gRows] at hrow
  | L n τ ih =>
    intro b r v hv row hrow
    rw [shapeOK_L, shapeL_iff] at hv
    have hnt : ntail n v = .atom 0 := tailO_some hv.2
    simp only [gRows, List.mem_cons] at hrow
    rcases hrow with rfl | rfl | hrow
    · refine ⟨rfl, by simp [LocalOK, localOK], ?_⟩
      simp only [readOK, decide_eq_true_eq]; rw [hnt]; exact hv.2
    · exact ⟨rfl, by simp [LocalOK, localOK, hnt], by simp [readOK]⟩
    · have hel : ∀ (js : List ℕ) (b : ℕ), (∀ j ∈ js, j < n) →
          ∀ row ∈ gElemsR (gRows c τ) (gSz τ) r v c b js, RowGood p s c row := by
        intro js
        induction js with
        | nil => intro b _ row hrow; simp [gElemsR] at hrow
        | cons j js ihj =>
          intro b hjs row hrow
          obtain ⟨w, hw, hok⟩ := hv.1 j (hjs j (by simp))
          have hwe := nthO_some hw
          simp only [gElemsR, List.mem_cons, List.mem_append] at hrow
          rcases hrow with rfl | hrow | hrow
          · refine ⟨rfl, by simp [LocalOK, localOK], ?_⟩
            simp only [readOK, decide_eq_true_eq]; rw [hwe]; exact hw
          · rw [hwe] at hrow; exact ih _ _ _ hok row hrow
          · exact ihj _ (fun j' hj' => hjs j' (by simp [hj'])) row hrow
      exact hel (List.range n) (b + 2) (fun j hj => List.mem_range.1 hj) row hrow

theorem inRows_good (T : Tpl) {p : ℕ} {s : Noun} {a : Fin T.k → Noun}
    (hs : ∀ i, Noun.slot (T.ax i) s = some (a i)) (ha : ∀ i, shapeOK p (T.inTy i) (a i) = true)
    (c : ℕ) : ∀ (is : List (Fin T.k)) (b : ℕ), ∀ row ∈ inRows T a c b is, RowGood p s c row := by
  intro is
  induction is with
  | nil => intro b row hrow; simp [inRows] at hrow
  | cons i is ih =>
    intro b row hrow
    simp only [inRows, List.mem_cons, List.mem_append] at hrow
    rcases hrow with rfl | hrow | hrow
    · exact ⟨rfl, by simp [LocalOK, localOK], by simp [readOK, hs i]⟩
    · exact gRows_good c _ _ _ _ (ha i) row hrow
    · exact ih _ row hrow

/-! ### The honest lookup -/

/-- Operands of the rows of `L` are served by rows of `R` with the right values. -/
def LinkIn (R L : List JRow) : Prop :=
  ∀ r ∈ L, (0 < r.node.op.arity → ∃ e ∈ R, e.node.id = r.node.a ∧ e.val = r.x) ∧
    (1 < r.node.op.arity → ∃ e ∈ R, e.node.id = r.node.b ∧ e.val = r.y)

theorem exRows_root {p k : ℕ} (ax : Fin k → ℕ) (a : Fin k → Noun) (c : ℕ) (e : Ex k) (b : ℕ) :
    ∃ r ∈ exRows p ax a c b e, r.node.id = b ∧ r.val = ev p a e := by
  cases e <;> exact ⟨_, List.mem_cons_self .., rfl, rfl⟩

theorem exRows_link {p k : ℕ} (ax : Fin k → ℕ) (a : Fin k → Noun) (c : ℕ) (R : List JRow) :
    ∀ (e : Ex k) (b : ℕ), (∀ r ∈ exRows p ax a c b e, r ∈ R) → LinkIn R (exRows p ax a c b e) := by
  intro e
  induction e with
  | var i => intro b _ r hr; simp only [exRows, List.mem_singleton] at hr; subst hr; simp [JOp.arity]
  | const n => intro b _ r hr; simp only [exRows, List.mem_singleton] at hr; subst hr; simp [JOp.arity]
  | add e₁ e₂ ih₁ ih₂ =>
    intro b hR r hr
    have s₁ : ∀ r ∈ exRows p ax a c (b + 1) e₁, r ∈ R := fun r h => hR r (by simp [exRows, h])
    have s₂ : ∀ r ∈ exRows p ax a c (b + 1 + exSz e₁) e₂, r ∈ R := fun r h => hR r (by simp [exRows, h])
    simp only [exRows, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | hr | hr
    · obtain ⟨r₁, h₁, i₁, v₁⟩ := exRows_root (p := p) ax a c e₁ (b + 1)
      obtain ⟨r₂, h₂, i₂, v₂⟩ := exRows_root (p := p) ax a c e₂ (b + 1 + exSz e₁)
      exact ⟨fun _ => ⟨r₁, s₁ _ h₁, i₁, v₁⟩, fun _ => ⟨r₂, s₂ _ h₂, i₂, v₂⟩⟩
    · exact ih₁ _ s₁ r hr
    · exact ih₂ _ s₂ r hr
  | mul e₁ e₂ ih₁ ih₂ =>
    intro b hR r hr
    have s₁ : ∀ r ∈ exRows p ax a c (b + 1) e₁, r ∈ R := fun r h => hR r (by simp [exRows, h])
    have s₂ : ∀ r ∈ exRows p ax a c (b + 1 + exSz e₁) e₂, r ∈ R := fun r h => hR r (by simp [exRows, h])
    simp only [exRows, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | hr | hr
    · obtain ⟨r₁, h₁, i₁, v₁⟩ := exRows_root (p := p) ax a c e₁ (b + 1)
      obtain ⟨r₂, h₂, i₂, v₂⟩ := exRows_root (p := p) ax a c e₂ (b + 1 + exSz e₁)
      exact ⟨fun _ => ⟨r₁, s₁ _ h₁, i₁, v₁⟩, fun _ => ⟨r₂, s₂ _ h₂, i₂, v₂⟩⟩
    · exact ih₁ _ s₁ r hr
    · exact ih₂ _ s₂ r hr
  | pair e₁ e₂ ih₁ ih₂ =>
    intro b hR r hr
    have s₁ : ∀ r ∈ exRows p ax a c (b + 1) e₁, r ∈ R := fun r h => hR r (by simp [exRows, h])
    have s₂ : ∀ r ∈ exRows p ax a c (b + 1 + exSz e₁) e₂, r ∈ R := fun r h => hR r (by simp [exRows, h])
    simp only [exRows, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | hr | hr
    · obtain ⟨r₁, h₁, i₁, v₁⟩ := exRows_root (p := p) ax a c e₁ (b + 1)
      obtain ⟨r₂, h₂, i₂, v₂⟩ := exRows_root (p := p) ax a c e₂ (b + 1 + exSz e₁)
      exact ⟨fun _ => ⟨r₁, s₁ _ h₁, i₁, v₁⟩, fun _ => ⟨r₂, s₂ _ h₂, i₂, v₂⟩⟩
    · exact ih₁ _ s₁ r hr
    · exact ih₂ _ s₂ r hr
  | nth j e ih =>
    intro b hR r hr
    have s₁ : ∀ r ∈ exRows p ax a c (b + 1) e, r ∈ R := fun r h => hR r (by simp [exRows, h])
    simp only [exRows, List.mem_cons] at hr
    rcases hr with rfl | hr
    · obtain ⟨r₁, h₁, i₁, v₁⟩ := exRows_root (p := p) ax a c e (b + 1)
      exact ⟨fun _ => ⟨r₁, s₁ _ h₁, i₁, v₁⟩, fun h => by simp [JOp.arity] at h⟩
    · exact ih _ s₁ r hr

theorem gRows_link (c : ℕ) (R : List JRow) : ∀ (τ : Ty) (b r : ℕ) (v : Noun),
    (∃ e ∈ R, e.node.id = r ∧ e.val = v) → (∀ row ∈ gRows c τ b r v, row ∈ R) →
      LinkIn R (gRows c τ b r v) := by
  intro τ
  induction τ with
  | F =>
    intro b r v hr _ row hrow
    simp only [gRows, List.mem_singleton] at hrow; subst hrow
    exact ⟨fun _ => hr, fun h => by simp [JOp.arity] at h⟩
  | N => intro b r v _ _ row hrow; simp [gRows] at hrow
  | L n τ ih =>
    intro b r v hr hR row hrow
    have hel : ∀ (js : List ℕ) (b : ℕ), (∀ row ∈ gElemsR (gRows c τ) (gSz τ) r v c b js, row ∈ R) →
        LinkIn R (gElemsR (gRows c τ) (gSz τ) r v c b js) := by
      intro js
      induction js with
      | nil => intro b _ row hrow; simp [gElemsR] at hrow
      | cons j js ihj =>
        intro b hR' row hrow
        have hme : (⟨⟨b, .nth j, r, 0⟩, c, nhd (ntail j v), v, z0⟩ : JRow) ∈ R :=
          hR' _ (by simp [gElemsR])
        simp only [gElemsR, List.mem_cons, List.mem_append] at hrow
        rcases hrow with rfl | hrow | hrow
        · exact ⟨fun _ => hr, fun h => by simp [JOp.arity] at h⟩
        · exact ih _ _ _ ⟨_, hme, rfl, rfl⟩ (fun x hx => hR' x (by simp [gElemsR, hx])) row hrow
        · exact ihj _ (fun x hx => hR' x (by simp [gElemsR, hx])) row hrow
    have hm0 : (⟨⟨b, .tlN n, r, 0⟩, c, ntail n v, v, z0⟩ : JRow) ∈ R := hR _ (by simp [gRows])
    simp only [gRows, List.mem_cons] at hrow
    rcases hrow with rfl | rfl | hrow
    · exact ⟨fun _ => hr, fun h => by simp [JOp.arity] at h⟩
    · exact ⟨fun _ => ⟨_, hm0, rfl, rfl⟩, fun h => by simp [JOp.arity] at h⟩
    · exact hel _ _ (fun x hx => hR x (by simp [gRows, hx])) row hrow

theorem inRows_link (T : Tpl) (a : Fin T.k → Noun) (c : ℕ) (R : List JRow) :
    ∀ (is : List (Fin T.k)) (b : ℕ), (∀ row ∈ inRows T a c b is, row ∈ R) →
      LinkIn R (inRows T a c b is) := by
  intro is
  induction is with
  | nil => intro b _ row hrow; simp [inRows] at hrow
  | cons i is ih =>
    intro b hR row hrow
    have hm0 : (⟨⟨b, .var i.val (T.ax i), 0, 0⟩, c, a i, z0, z0⟩ : JRow) ∈ R := hR _ (by simp [inRows])
    simp only [inRows, List.mem_cons, List.mem_append] at hrow
    rcases hrow with rfl | hrow | hrow
    · simp [JOp.arity]
    · exact gRows_link c R _ _ _ _ ⟨_, hm0, rfl, rfl⟩ (fun x hx => hR x (by simp [inRows, hx])) row hrow
    · exact ih _ (fun x hx => hR x (by simp [inRows, hx])) row hrow

theorem getElem?_of_ids {R : List JRow} {N : ℕ}
    (hR : R.map (fun r => r.node.id) = List.range' 0 N) {r : JRow} (hr : r ∈ R) :
    R[r.node.id]? = some r := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hlen : R.length = N := by simpa using congrArg List.length hR
  have h2 := congrArg (fun L => L[i]?) hR
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some,
    List.getElem?_range', hlen ▸ hi, if_true] at h2
  simp only [zero_add, one_mul, Option.some.injEq] at h2
  rw [h2]
  exact List.getElem?_eq_getElem hi

theorem honestRows_ids (p : ℕ) (T : Tpl) (s : Noun) (c : ℕ) :
    (honestRows p T s c).map (fun r => r.node.id) =
      List.range' 0 (exSz T.body + inSz T (List.finRange T.k)) := by
  rw [← nodesOf_ids, ← honestRows_nodes p T s c, List.map_map]
  rfl

theorem argsD_eq {T : Tpl} {s : Noun} {a : Fin T.k → Noun}
    (hs : ∀ i, Noun.slot (T.ax i) s = some (a i)) : argsD T s = a := by
  funext i; simp [argsD, hs i]

/-- **`interp_complete`: the honest jet table for a call is accepted by every interpreter check.**
For a well-typed template `T` over a positive modulus `p`, if `T.sem p s = some r`, then the honest rows of call
`c` (`honestRows p T s c`) are exactly that call's rows, carry the canonical node skeleton of `T`, satisfy every
local constraint, are served by a functional node-value lookup, have genuine reads for `s`, and contain an output
row (node `0`) whose value is `r`. -/
theorem interp_complete {p : ℕ} (hp : 0 < p) (T : Tpl) (hT : T.WellTyped p) (s r : Noun) (c : ℕ)
    (h : T.sem p s = some r) :
    callRows (honestRows p T s c) c = honestRows p T s c ∧
    (honestRows p T s c).map JRow.node = nodesOf T ∧
    (∀ row ∈ honestRows p T s c, LocalOK p row) ∧
    NodeLookupSound (honestRows p T s c) ∧
    ReadsGenuine s (honestRows p T s c) ∧
    ∃ out ∈ honestRows p T s c, out.node.id = 0 ∧ out.val = r := by
  obtain ⟨a, hs, ha, hr⟩ := sem_eq_some_iff.1 h
  have hA := argsD_eq hs
  have hgood : ∀ row ∈ honestRows p T s c, RowGood p s c row := by
    intro row hrow
    simp only [honestRows, List.mem_append, hA] at hrow
    rcases hrow with hrow | hrow
    · exact exRows_good hp hs ha c hT 0 row hrow
    · exact inRows_good T hs ha c _ _ row hrow
  set R := honestRows p T s c with hRdef
  have hlink : LinkIn R R := by
    intro row hrow
    have hrow' := hrow
    simp only [hRdef, honestRows, List.mem_append] at hrow'
    rcases hrow' with hrow' | hrow'
    · exact exRows_link (p := p) T.ax _ c R T.body 0
        (fun x hx => by simp only [hRdef, honestRows, List.mem_append]; exact Or.inl hx) row hrow'
    · exact inRows_link T _ c R _ _
        (fun x hx => by simp only [hRdef, honestRows, List.mem_append]; exact Or.inr hx) row hrow'
  have hids := honestRows_ids p T s c
  rw [← hRdef] at hids
  refine ⟨?_, honestRows_nodes p T s c, fun row hrow => (hgood row hrow).2.1, ?_,
    fun row hrow => (hgood row hrow).2.2, ?_⟩
  · exact List.filter_eq_self.2 fun row hrow => by simp [(hgood row hrow).1]
  · refine ⟨fun id => ((R[id]?).map JRow.val).getD z0, fun row hrow => ?_, fun row hrow => ?_⟩
    · simp [getElem?_of_ids hids hrow]
    · obtain ⟨hx, hy⟩ := hlink row hrow
      refine ⟨fun h0 => ?_, fun h1 => ?_⟩
      · obtain ⟨e, he, hid, hv⟩ := hx h0
        dsimp only; rw [← hid, getElem?_of_ids hids he]; simp [hv]
      · obtain ⟨e, he, hid, hv⟩ := hy h1
        dsimp only; rw [← hid, getElem?_of_ids hids he]; simp [hv]
  · obtain ⟨e, he, hid, hv⟩ := exRows_root (p := p) T.ax (argsD T s) c T.body 0
    refine ⟨e, ?_, hid, ?_⟩
    · simp only [hRdef, honestRows, List.mem_append]; exact Or.inl he
    · rw [hv, hA, hr]

/-! ## §6 Matmul instance -/

/-- Row count of the matmul template (computed). -/
def matmulRows (n : ℕ) : ℕ := (nodesOf (matmulT n)).length

/-- The honest table of the 2×2 toy (`p = 7`, J-2's `toyS`, call `0`). -/
def toyRows : List JRow := honestRows 7 (matmulT 2) toyS 0

theorem toyRows_length : toyRows.length = 103 := by decide +kernel

/-- Row counts: `n = 2` 103 (body 69 + guards 2·17), `n = 8` 4,423 (body 4,113 + guards 2·155). -/
theorem matmul2_rows : matmulRows 2 = 103 := by decide +kernel
theorem matmul8_rows : matmulRows 8 = 4423 := by decide +kernel
theorem matmul8_body : exSz (matmulT 8).body = 4113 := by decide +kernel

/-- The honest table satisfies everything; its output is `toyC`. -/
theorem toy_complete :
    callRows toyRows 0 = toyRows ∧ toyRows.map JRow.node = nodesOf (matmulT 2) ∧
    (∀ row ∈ toyRows, LocalOK 7 row) ∧ NodeLookupSound toyRows ∧ ReadsGenuine toyS toyRows ∧
    ∃ out ∈ toyRows, out.node.id = 0 ∧ out.val = toyC :=
  interp_complete (by norm_num) (matmulT 2) (matmul_wellTyped (by norm_num) 2) toyS toyC 0 toy_sem

/-- From the soundness side: any table whose call-0 rows pass the constraints has output `toyC`. -/
theorem toy_sound_output (t : JTable) (hsk : (callRows t 0).map JRow.node = nodesOf (matmulT 2))
    (hloc : ∀ r ∈ callRows t 0, LocalOK 7 r) (hlk : NodeLookupSound (callRows t 0))
    (hrd : ReadsGenuine toyS (callRows t 0)) (out : JRow) (hout : out ∈ callRows t 0)
    (hid : out.node.id = 0) : out.val = toyC := by
  have := (interp_sound (by norm_num) (matmulT 2) (matmul_wellTyped (by norm_num) 2) toyS t 0 hsk hloc
    hlk hrd out hout hid).1
  rw [toy_sem] at this
  exact (Option.some.inj this).symm

/-- The honest row 3: the first `mul` (entry (0,0), `A₀₀·B₀₀ = 1·5`). -/
theorem toyRow3 : toyRows[3]? = some ⟨⟨3, .mul, 4, 7⟩, 0, .atom 5, .atom 1, .atom 5⟩ := by
  decide +kernel

/-- **One tampered row**: row 3 claims `1·5 = 6`. -/
def badRow : JRow := ⟨⟨3, .mul, 4, 7⟩, 0, .atom 6, .atom 1, .atom 5⟩

def toyTampered : List JRow := toyRows.set 3 badRow

theorem badRow_mem : badRow ∈ toyTampered := by
  unfold toyTampered
  exact List.mem_of_getElem? (List.getElem?_set_self (by rw [toyRows_length]; omega))

/-- **The tampered table is rejected**: its degree-2 gate fails on row 3. -/
theorem toyTampered_rejected : ¬ ∀ row ∈ toyTampered, LocalOK 7 row :=
  fun h => absurd (h badRow badRow_mem) (by unfold LocalOK; decide)

end Nock.Jet.Interp
