/-
  Nock/Jet/Autogen.lean

  **The template language `Tpl`, the compiler
  `compile : Tpl → Noun`, and ONE generic faithfulness theorem.**

  Scope: loop-free templates only.

  * **§1 language.**  `Ty` (`F` field atom `< p`; `L n τ` null-terminated list of exactly `n`
    elements), `Ex k` (`var`, `const`, `add`, `mul`, `nth`, `pair`; the spec's `build es` is the
    derived `Ex.build := foldr pair (const 0)`, which compiles to exactly the spec's autocons
    chain `[⟦e₀⟧ [… [1 0]]]`), `HasTy` / `WellTyped` (p-parametric: a field constant must be
    `< p`), `shapeOK`, `ev`, `Tpl`, `Tpl.toTemplate p : Template` (J-1's shape, used as is),
    `Tpl.sem p T := (T.toTemplate p).semS`.
  * **§2 compiler.**  `LIB p` (battery `[isf [fadl [subc fmll]]]`, arms at core axes 4/10/22/23,
    recursion by rebuilding the core and op 9 — never op 10), `cEx` (expressions on `σ = [LIB s]`),
    `gTy` (shape guards), `guardAll`, `compile p T = [8 [1 LIB] [6 GUARD BODY [0 0]]]`.
  * **§3 proof.**  `EvalsTo X F v := ∃ fuel, evalN fuel X F = some v` with one rule per opcode
    (positive direction, fuels joined by `evalN_mono`); the four library specs `isf_spec`,
    `subc_spec`, `fadl_spec`, `fmll_spec` (counter inductions); `ev_spec`, `guard_spec`,
    `guardAll_spec`; `compile_faithful`, `compile_complete` (inversion ONLY on the op-8/op-6/op-7
    shells, the guard's first read and `slot 0 = none`, then `evalN_deterministic`; no inversion on
    any arithmetic arm), `compile_crash_exact`, and the J-1 registry-entry theorem
    `compile_jetSpec_faithful`.
-/
import Nock.Jet.Semantics

set_option autoImplicit false

namespace Nock.Jet.Autogen

open Nock Nock.Noun

/-! ## §1 The template language -/

/-- Value types: a field atom (`< p`), or a null-terminated list of exactly `n` elements. -/
inductive Ty where
  | F : Ty
  | L : ℕ → Ty → Ty
  | N : Ty
  deriving DecidableEq, Repr

/-- Loop-free first-order expressions over `k` arguments. -/
inductive Ex (k : ℕ) where
  | var : Fin k → Ex k
  | const : ℕ → Ex k
  | add : Ex k → Ex k → Ex k
  | mul : Ex k → Ex k → Ex k
  | nth : ℕ → Ex k → Ex k
  | pair : Ex k → Ex k → Ex k
  deriving Repr

/-- The spec's `build [e₀ … e_{m−1}]`: the null-terminated list, as a derived form. -/
def Ex.build {k : ℕ} (es : List (Ex k)) : Ex k := es.foldr .pair (.const 0)

/-- Typing (p-parametric: a field constant is an atom `< p`). -/
inductive HasTy (p : ℕ) {k : ℕ} (inTy : Fin k → Ty) : Ex k → Ty → Prop
  | var (i : Fin k) : HasTy p inTy (.var i) (inTy i)
  | const {c : ℕ} : c < p → HasTy p inTy (.const c) .F
  | nil (τ : Ty) : HasTy p inTy (.const 0) (.L 0 τ)
  | add {e₁ e₂ : Ex k} : HasTy p inTy e₁ .F → HasTy p inTy e₂ .F → HasTy p inTy (.add e₁ e₂) .F
  | mul {e₁ e₂ : Ex k} : HasTy p inTy e₁ .F → HasTy p inTy e₂ .F → HasTy p inTy (.mul e₁ e₂) .F
  | nth {j n : ℕ} {τ : Ty} {e : Ex k} : HasTy p inTy e (.L n τ) → j < n → HasTy p inTy (.nth j e) τ
  | pair {e₁ e₂ : Ex k} {n : ℕ} {τ : Ty} :
      HasTy p inTy e₁ τ → HasTy p inTy e₂ (.L n τ) → HasTy p inTy (.pair e₁ e₂) (.L (n + 1) τ)
  | weakN {e : Ex k} {τ : Ty} : HasTy p inTy e τ → HasTy p inTy e .N

/-- List shape over an element predicate. -/
def shapeL (ok : Noun → Bool) : ℕ → Noun → Bool
  | 0, v => decide (v = .atom 0)
  | _ + 1, .atom _ => false
  | n + 1, .cell h t => ok h && shapeL ok n t

/-- The decidable shape predicate (the template's domain on each argument). -/
def shapeOK (p : ℕ) : Ty → Noun → Bool
  | .F, .atom v => decide (v < p)
  | .F, .cell _ _ => false
  | .L n τ, v => shapeL (shapeOK p τ) n v
  | .N, _ => true

def nhd : Noun → Noun
  | .cell h _ => h
  | .atom _ => .atom 0

def ntl : Noun → Noun
  | .cell _ t => t
  | .atom _ => .atom 0

def ntail : ℕ → Noun → Noun
  | 0, v => v
  | j + 1, v => ntl (ntail j v)

def atomVal : Noun → ℕ
  | .atom v => v
  | .cell _ _ => 0

/-- The evaluator: a TOTAL Lean function (junk off shape; never reached under `shapeOK`). -/
def ev (p : ℕ) {k : ℕ} (a : Fin k → Noun) : Ex k → Noun
  | .var i => a i
  | .const c => .atom c
  | .add e₁ e₂ => .atom ((atomVal (ev p a e₁) + atomVal (ev p a e₂)) % p)
  | .mul e₁ e₂ => .atom ((atomVal (ev p a e₁) * atomVal (ev p a e₂)) % p)
  | .nth j e => nhd (ntail j (ev p a e))
  | .pair e₁ e₂ => .cell (ev p a e₁) (ev p a e₂)

/-- A template: argument axes, argument types, output type, body. -/
structure Tpl where
  k : ℕ
  ax : Fin k → ℕ
  inTy : Fin k → Ty
  outTy : Ty
  body : Ex k

/-- Well-typedness of a template at modulus `p`. -/
def Tpl.WellTyped (p : ℕ) (T : Tpl) : Prop := HasTy p T.inTy T.body T.outTy

/-- The J-1 `Template` of a `Tpl`: same arity and axes; `sem` = guard then evaluate. -/
def Tpl.toTemplate (p : ℕ) (T : Tpl) : Template where
  k := T.k
  ax := T.ax
  sem a := if ∀ i, shapeOK p (T.inTy i) (a i) = true then some (ev p a T.body) else none

/-- The extractable semantics on a subject. -/
def Tpl.sem (p : ℕ) (T : Tpl) (s : Noun) : Option Noun := (T.toTemplate p).semS s

/-! ## §2 The compiler -/

def A (n : ℕ) : Noun := .atom n
def op0 (ax : ℕ) : Noun := .cell (.atom 0) (.atom ax)
def op1 (c : Noun) : Noun := .cell (.atom 1) c
def op3 (f : Noun) : Noun := .cell (.atom 3) f
def op4 (f : Noun) : Noun := .cell (.atom 4) f
def op5 (f g : Noun) : Noun := .cell (.atom 5) (.cell f g)
def op6 (b c d : Noun) : Noun := .cell (.atom 6) (.cell b (.cell c d))
def op7 (f g : Noun) : Noun := .cell (.atom 7) (.cell f g)
def op8 (f g : Noun) : Noun := .cell (.atom 8) (.cell f g)
def op9 (ax : ℕ) (f : Noun) : Noun := .cell (.atom 9) (.cell (.atom ax) f)

/-- `CALL(arm, S, ctx) = [9 arm [[0 2] [S ctx]]]`: build the core `[battery [S ctx]]`, run the arm. -/
def call (arm : ℕ) (S C : Noun) : Noun := op9 arm (.cell (op0 2) (.cell S C))

/-- `isf (v@12, c@13)`: `0` if `v < p` (counting `c` up to `v` before `p − 1`), else `1`. -/
def isfArm (p : ℕ) : Noun :=
  op6 (op5 (op0 13) (op0 12)) (op1 (A 0))
    (op6 (op5 (op0 13) (op1 (A (p - 1)))) (op1 (A 1))
      (call 4 (.cell (op0 12) (op4 (op0 13))) (op0 7)))

/-- `subc (c@12, d@26, a@27)`: `c + (a − d)` by counting `(c, d)` up until `d = a`. -/
def subcArm : Noun :=
  op6 (op5 (op0 26) (op0 27)) (op0 12)
    (call 22 (.cell (op4 (op0 12)) (.cell (op4 (op0 26)) (op0 27))) (op0 7))

/-- `fadl (x@12, y@26, b@27)`: `(x + (b − y)) % p`, walking `x` up, wrapping via `subc`. -/
def fadlArm (p : ℕ) : Noun :=
  op6 (op5 (op0 26) (op0 27)) (op0 12)
    (op6 (op5 (op0 12) (op1 (A (p - 1))))
      (call 22 (.cell (op1 (A 0)) (.cell (op4 (op0 26)) (op0 27))) (op0 7))
      (call 10 (.cell (op4 (op0 12)) (.cell (op4 (op0 26)) (op0 27))) (op0 7)))

/-- `fmll (acc@12, c@26, a@54, b@55)`: `(acc + a·(b − c)) % p`, by `b − c` calls of `fadl`. -/
def fmllArm : Noun :=
  op6 (op5 (op0 26) (op0 55)) (op0 12)
    (call 23 (.cell (call 10 (.cell (op0 12) (.cell (op1 (A 0)) (op0 54))) (op0 7))
                    (.cell (op4 (op0 26)) (.cell (op0 54) (op0 55)))) (op0 7))

/-- The library battery `[isf [fadl [subc fmll]]]`. -/
def LIB (p : ℕ) : Noun := .cell (isfArm p) (.cell (fadlArm p) (.cell subcArm fmllArm))

/-- `tail^j f`. -/
def tailF : ℕ → Noun → Noun
  | 0, f => f
  | j + 1, f => op7 (tailF j f) (op0 3)

/-- Expressions, as formulas on `σ = [LIB s]`. -/
def cEx {k : ℕ} (ax : Fin k → ℕ) : Ex k → Noun
  | .var i => op7 (op0 3) (op0 (ax i))
  | .const c => op1 (A c)
  | .add e₁ e₂ => call 10 (.cell (cEx ax e₁) (.cell (op1 (A 0)) (cEx ax e₂))) (op0 1)
  | .mul e₁ e₂ => call 23 (.cell (op1 (A 0)) (.cell (op1 (A 0)) (.cell (cEx ax e₁) (cEx ax e₂)))) (op0 1)
  | .nth j e => op7 (tailF j (cEx ax e)) (op0 2)
  | .pair e₁ e₂ => .cell (cEx ax e₁) (cEx ax e₂)

/-- List guard over an element guard `g`. -/
def gL (g : Noun → Noun) : ℕ → Noun → Noun
  | 0, f => op5 f (op1 (A 0))
  | n + 1, f => op6 (op3 f) (op6 (g (op7 f (op0 2))) (gL g n (op7 f (op0 3))) (op1 (A 1))) (op1 (A 1))

/-- Shape guards: `G τ f` returns `0` iff the value of `f` has shape `τ`, else `1`. -/
def gTy (p : ℕ) : Ty → Noun → Noun
  | .F, f => op6 (op3 f) (op1 (A 1)) (call 4 (.cell f (op1 (A 0))) (op0 1))
  | .L n τ, f => gL (gTy p τ) n f
  | .N, f => op6 (op3 f) (op1 (A 0)) (op1 (A 0))

/-- The conjunction of the argument guards, in the order of `l` (`and g h = [6 g h [1 1]]`,
right-nested, no trailing seed; `[1 0]` only for zero arguments). -/
def guardAll (p : ℕ) (T : Tpl) : List (Fin T.k) → Noun
  | [] => op1 (A 0)
  | [i] => gTy p (T.inTy i) (cEx T.ax (.var i))
  | i :: j :: l => op6 (gTy p (T.inTy i) (cEx T.ax (.var i))) (guardAll p T (j :: l)) (op1 (A 1))

/-- **The compiler**: `c_T = [8 [1 LIB] [6 GUARD BODY [0 0]]]`. -/
def compile (p : ℕ) (T : Tpl) : Noun :=
  op8 (op1 (LIB p)) (op6 (guardAll p T (List.finRange T.k)) (cEx T.ax T.body) (op0 0))

/-- Canonical: a pure function of `(p, T)`. -/
theorem compile_canonical (p : ℕ) (T : Tpl) : compile p T = compile p T := rfl

/-! ## §3 Positive evaluation rules -/

/-- `F` evaluates on `X` to `v` at some fuel. -/
def EvalsTo (X F v : Noun) : Prop := ∃ fuel, evalN fuel X F = some v

theorem EvalsTo.det {X F v w : Noun} (h₁ : EvalsTo X F v) (h₂ : EvalsTo X F w) : v = w := by
  obtain ⟨f₁, h₁⟩ := h₁; obtain ⟨f₂, h₂⟩ := h₂
  exact evalN_deterministic h₁ h₂

theorem EvalsTo.slot {X v : Noun} {ax : ℕ} (h : Noun.slot ax X = some v) : EvalsTo X (op0 ax) v :=
  ⟨1, by simp [op0, evalN, h]⟩

theorem EvalsTo.quote (X c : Noun) : EvalsTo X (op1 c) c := ⟨1, by simp [op1, evalN]⟩

theorem EvalsTo.cons {X a b d va vd : Noun} (h₁ : EvalsTo X (.cell a b) va) (h₂ : EvalsTo X d vd) :
    EvalsTo X (.cell (.cell a b) d) (.cell va vd) := by
  obtain ⟨f₁, h₁⟩ := h₁; obtain ⟨f₂, h₂⟩ := h₂
  refine ⟨max f₁ f₂ + 1, ?_⟩
  simp [evalN, evalN_mono (Nat.le_max_left f₁ f₂) h₁, evalN_mono (Nat.le_max_right f₁ f₂) h₂]

theorem EvalsTo.op3 {X f v : Noun} (h : EvalsTo X f v) : EvalsTo X (op3 f) (wut v) := by
  obtain ⟨f₁, h⟩ := h
  exact ⟨f₁ + 1, by simp [Autogen.op3, evalN, h]⟩

theorem EvalsTo.op4 {X f : Noun} {n : ℕ} (h : EvalsTo X f (.atom n)) :
    EvalsTo X (op4 f) (.atom (n + 1)) := by
  obtain ⟨f₁, h⟩ := h
  exact ⟨f₁ + 1, by simp [Autogen.op4, evalN, h, lus]⟩

theorem EvalsTo.op5 {X f g v w : Noun} (h₁ : EvalsTo X f v) (h₂ : EvalsTo X g w) :
    EvalsTo X (op5 f g) (tis v w) := by
  obtain ⟨f₁, h₁⟩ := h₁; obtain ⟨f₂, h₂⟩ := h₂
  refine ⟨max f₁ f₂ + 1, ?_⟩
  simp [Autogen.op5, evalN, evalN_mono (Nat.le_max_left f₁ f₂) h₁,
    evalN_mono (Nat.le_max_right f₁ f₂) h₂]

theorem EvalsTo.op6t {X b c d v : Noun} (h₁ : EvalsTo X b (.atom 0)) (h₂ : EvalsTo X c v) :
    EvalsTo X (op6 b c d) v := by
  obtain ⟨f₁, h₁⟩ := h₁; obtain ⟨f₂, h₂⟩ := h₂
  refine ⟨max f₁ f₂ + 1, ?_⟩
  simp [Autogen.op6, evalN, evalN_mono (Nat.le_max_left f₁ f₂) h₁,
    evalN_mono (Nat.le_max_right f₁ f₂) h₂]

theorem EvalsTo.op6f {X b c d v : Noun} (h₁ : EvalsTo X b (.atom 1)) (h₂ : EvalsTo X d v) :
    EvalsTo X (op6 b c d) v := by
  obtain ⟨f₁, h₁⟩ := h₁; obtain ⟨f₂, h₂⟩ := h₂
  refine ⟨max f₁ f₂ + 1, ?_⟩
  simp [Autogen.op6, evalN, evalN_mono (Nat.le_max_left f₁ f₂) h₁,
    evalN_mono (Nat.le_max_right f₁ f₂) h₂]

theorem EvalsTo.op7 {X f g v w : Noun} (h₁ : EvalsTo X f v) (h₂ : EvalsTo v g w) :
    EvalsTo X (op7 f g) w := by
  obtain ⟨f₁, h₁⟩ := h₁; obtain ⟨f₂, h₂⟩ := h₂
  refine ⟨max f₁ f₂ + 1, ?_⟩
  simp [Autogen.op7, evalN, evalN_mono (Nat.le_max_left f₁ f₂) h₁,
    evalN_mono (Nat.le_max_right f₁ f₂) h₂]

theorem EvalsTo.op8 {X f g v w : Noun} (h₁ : EvalsTo X f v) (h₂ : EvalsTo (.cell v X) g w) :
    EvalsTo X (op8 f g) w := by
  obtain ⟨f₁, h₁⟩ := h₁; obtain ⟨f₂, h₂⟩ := h₂
  refine ⟨max f₁ f₂ + 1, ?_⟩
  simp [Autogen.op8, evalN, evalN_mono (Nat.le_max_left f₁ f₂) h₁,
    evalN_mono (Nat.le_max_right f₁ f₂) h₂]

theorem EvalsTo.op9 {X F core arm w : Noun} {ax : ℕ} (h₁ : EvalsTo X F core)
    (ha : Noun.slot ax core = some arm) (h₂ : EvalsTo core arm w) : EvalsTo X (op9 ax F) w := by
  obtain ⟨f₁, h₁⟩ := h₁; obtain ⟨f₂, h₂⟩ := h₂
  refine ⟨max f₁ f₂ + 1, ?_⟩
  simp [Autogen.op9, evalN, evalN_mono (Nat.le_max_left f₁ f₂) h₁, ha,
    evalN_mono (Nat.le_max_right f₁ f₂) h₂]

/-- The core-building call: `[9 arm [[0 2] [S C]]]` on a subject whose axis 2 is the battery. -/
theorem EvalsTo.call {X S₁ S₂ C L sv cv arm w : Noun} {ax : ℕ}
    (hL : Noun.slot 2 X = some L) (hS : EvalsTo X (.cell S₁ S₂) sv) (hC : EvalsTo X C cv)
    (ha : Noun.slot ax (.cell L (.cell sv cv)) = some arm)
    (h : EvalsTo (.cell L (.cell sv cv)) arm w) : EvalsTo X (call ax (.cell S₁ S₂) C) w :=
  EvalsTo.op9 (EvalsTo.cons (EvalsTo.slot hL) (EvalsTo.cons hS hC)) ha h

/-! ### Core slots -/

/-- An arm's core `[LIB [sample ctx]]`. -/
abbrev core (p : ℕ) (samp ctx : Noun) : Noun := .cell (LIB p) (.cell samp ctx)

theorem slot_isf (p : ℕ) (X : Noun) : Noun.slot 4 (.cell (LIB p) X) = some (isfArm p) := by
  simp [LIB, Noun.slot]
theorem slot_fadl (p : ℕ) (X : Noun) : Noun.slot 10 (.cell (LIB p) X) = some (fadlArm p) := by
  simp [LIB, Noun.slot]
theorem slot_subc (p : ℕ) (X : Noun) : Noun.slot 22 (.cell (LIB p) X) = some subcArm := by
  simp [LIB, Noun.slot]
theorem slot_fmll (p : ℕ) (X : Noun) : Noun.slot 23 (.cell (LIB p) X) = some fmllArm := by
  simp [LIB, Noun.slot]

theorem tis_atom (m n : ℕ) : tis (.atom m) (.atom n) = .atom (if m = n then 0 else 1) := by
  by_cases h : m = n <;> simp [tis, h]

/-! ## §3.1 Library specs (positive direction, counter inductions) -/

/-- **`isf_spec`**: from any counter `c ≤ p − 1`, `isf` returns `0` iff `c ≤ v < p`. -/
theorem isf_spec {p : ℕ} (hp : 0 < p) :
    ∀ (d c v : ℕ) (ctx : Noun), p - 1 - c = d → c ≤ p - 1 →
      EvalsTo (core p (.cell (.atom v) (.atom c)) ctx) (isfArm p)
        (.atom (if c ≤ v ∧ v < p then 0 else 1)) := by
  intro d
  induction d with
  | zero =>
    intro c v ctx hd hc
    have hcp : c = p - 1 := by omega
    unfold isfArm
    by_cases hcv : c = v
    · refine EvalsTo.op6t ?_ ?_
      · have := EvalsTo.op5 (X := core p (.cell (.atom v) (.atom c)) ctx)
          (EvalsTo.slot (ax := 13) (v := .atom c) (by simp [Noun.slot]))
          (EvalsTo.slot (ax := 12) (v := .atom v) (by simp [Noun.slot]))
        simpa [tis_atom, hcv] using this
      · have : (if c ≤ v ∧ v < p then 0 else 1) = 0 := by rw [if_pos]; omega
        rw [this]; exact EvalsTo.quote _ _
    · refine EvalsTo.op6f ?_ (EvalsTo.op6t ?_ ?_)
      · have := EvalsTo.op5 (X := core p (.cell (.atom v) (.atom c)) ctx)
          (EvalsTo.slot (ax := 13) (v := .atom c) (by simp [Noun.slot]))
          (EvalsTo.slot (ax := 12) (v := .atom v) (by simp [Noun.slot]))
        simpa [tis_atom, hcv] using this
      · have := EvalsTo.op5 (X := core p (.cell (.atom v) (.atom c)) ctx)
          (EvalsTo.slot (ax := 13) (v := .atom c) (by simp [Noun.slot]))
          (EvalsTo.quote _ (A (p - 1)))
        simpa [A, tis_atom, hcp] using this
      · have : (if c ≤ v ∧ v < p then 0 else 1) = 1 := by rw [if_neg]; omega
        rw [this]; exact EvalsTo.quote _ _
  | succ d ih =>
    intro c v ctx hd hc
    unfold isfArm
    by_cases hcv : c = v
    · refine EvalsTo.op6t ?_ ?_
      · have := EvalsTo.op5 (X := core p (.cell (.atom v) (.atom c)) ctx)
          (EvalsTo.slot (ax := 13) (v := .atom c) (by simp [Noun.slot]))
          (EvalsTo.slot (ax := 12) (v := .atom v) (by simp [Noun.slot]))
        simpa [tis_atom, hcv] using this
      · have : (if c ≤ v ∧ v < p then 0 else 1) = 0 := by rw [if_pos]; omega
        rw [this]; exact EvalsTo.quote _ _
    · have hcp : c ≠ p - 1 := by omega
      refine EvalsTo.op6f ?_ (EvalsTo.op6f ?_ ?_)
      · have := EvalsTo.op5 (X := core p (.cell (.atom v) (.atom c)) ctx)
          (EvalsTo.slot (ax := 13) (v := .atom c) (by simp [Noun.slot]))
          (EvalsTo.slot (ax := 12) (v := .atom v) (by simp [Noun.slot]))
        simpa [tis_atom, hcv] using this
      · have := EvalsTo.op5 (X := core p (.cell (.atom v) (.atom c)) ctx)
          (EvalsTo.slot (ax := 13) (v := .atom c) (by simp [Noun.slot]))
          (EvalsTo.quote _ (A (p - 1)))
        simpa [A, tis_atom, hcp] using this
      · have hrec := ih (c + 1) v ctx (by omega) (by omega)
        have heq : (if c ≤ v ∧ v < p then 0 else 1) = (if c + 1 ≤ v ∧ v < p then 0 else 1) := by
          split_ifs <;> omega
        rw [heq]
        refine EvalsTo.call (L := LIB p) (sv := .cell (.atom v) (.atom (c + 1))) (cv := ctx)
          (by simp [Noun.slot]) ?_ ?_ (slot_isf p _) hrec
        · exact EvalsTo.cons (EvalsTo.slot (by simp [Noun.slot]))
            (EvalsTo.op4 (EvalsTo.slot (by simp [Noun.slot])))
        · exact EvalsTo.slot (by simp [Noun.slot])

/-- Shorthand for the two-read equality test inside a core. -/
theorem evEqTest {X : Noun} (a b : ℕ) {m n : ℕ} (ha : Noun.slot a X = some (.atom m))
    (hb : Noun.slot b X = some (.atom n)) :
    EvalsTo X (op5 (op0 a) (op0 b)) (.atom (if m = n then 0 else 1)) := by
  have := EvalsTo.op5 (EvalsTo.slot ha) (EvalsTo.slot hb)
  rwa [tis_atom] at this

theorem evEqConst {X : Noun} (a : ℕ) {m n : ℕ} (ha : Noun.slot a X = some (.atom m)) :
    EvalsTo X (op5 (op0 a) (op1 (A n))) (.atom (if m = n then 0 else 1)) := by
  have := EvalsTo.op5 (EvalsTo.slot ha) (EvalsTo.quote X (A n))
  rwa [A, tis_atom] at this

theorem EvalsTo.ite0 {X F : Noun} {P : Prop} [Decidable P] (hP : P)
    (h : EvalsTo X F (.atom (if P then 0 else 1))) : EvalsTo X F (.atom 0) := by
  rwa [if_pos hP] at h

theorem EvalsTo.ite1 {X F : Noun} {P : Prop} [Decidable P] (hP : ¬ P)
    (h : EvalsTo X F (.atom (if P then 0 else 1))) : EvalsTo X F (.atom 1) := by
  rwa [if_neg hP] at h

/-- **`subc_spec`**: `subc (c, d, a) = c + (a − d)` for `d ≤ a`. -/
theorem subc_spec (p : ℕ) :
    ∀ (m c dd a : ℕ) (ctx : Noun), a - dd = m → dd ≤ a →
      EvalsTo (core p (.cell (.atom c) (.cell (.atom dd) (.atom a))) ctx) subcArm
        (.atom (c + (a - dd))) := by
  intro m
  induction m with
  | zero =>
    intro c dd a ctx hm hda
    have hd : dd = a := by omega
    unfold subcArm
    refine EvalsTo.op6t (EvalsTo.ite0 hd (evEqTest 26 27 (by simp [Noun.slot]) (by simp [Noun.slot])))
      ?_
    rw [show c + (a - dd) = c by omega]
    exact EvalsTo.slot (by simp [Noun.slot])
  | succ m ih =>
    intro c dd a ctx hm hda
    have hd : ¬ dd = a := by omega
    unfold subcArm
    refine EvalsTo.op6f (EvalsTo.ite1 hd (evEqTest 26 27 (by simp [Noun.slot]) (by simp [Noun.slot])))
      ?_
    have hrec := ih (c + 1) (dd + 1) a ctx (by omega) (by omega)
    rw [show c + (a - dd) = c + 1 + (a - (dd + 1)) by omega]
    refine EvalsTo.call (L := LIB p) (sv := .cell (.atom (c + 1)) (.cell (.atom (dd + 1)) (.atom a)))
      (cv := ctx) (by simp [Noun.slot]) ?_ (EvalsTo.slot (by simp [Noun.slot])) (slot_subc p _) hrec
    exact EvalsTo.cons (EvalsTo.op4 (EvalsTo.slot (by simp [Noun.slot])))
      (EvalsTo.cons (EvalsTo.op4 (EvalsTo.slot (by simp [Noun.slot])))
        (EvalsTo.slot (by simp [Noun.slot])))

/-- **`fadl_spec`**: `fadl (x, y, b) = (x + (b − y)) % p` for `x < p`, `y ≤ b < p`. -/
theorem fadl_spec {p : ℕ} (hp : 0 < p) :
    ∀ (m x y b : ℕ) (ctx : Noun), b - y = m → y ≤ b → b < p → x < p →
      EvalsTo (core p (.cell (.atom x) (.cell (.atom y) (.atom b))) ctx) (fadlArm p)
        (.atom ((x + (b - y)) % p)) := by
  intro m
  induction m with
  | zero =>
    intro x y b ctx hm hyb hb hx
    have hd : y = b := by omega
    unfold fadlArm
    refine EvalsTo.op6t (EvalsTo.ite0 hd (evEqTest 26 27 (by simp [Noun.slot]) (by simp [Noun.slot])))
      ?_
    rw [show (x + (b - y)) % p = x by rw [show b - y = 0 by omega, Nat.add_zero, Nat.mod_eq_of_lt hx]]
    exact EvalsTo.slot (by simp [Noun.slot])
  | succ m ih =>
    intro x y b ctx hm hyb hb hx
    have hd : ¬ y = b := by omega
    unfold fadlArm
    refine EvalsTo.op6f (EvalsTo.ite1 hd (evEqTest 26 27 (by simp [Noun.slot]) (by simp [Noun.slot])))
      ?_
    by_cases hxp : x = p - 1
    · refine EvalsTo.op6t (EvalsTo.ite0 hxp (evEqConst 12 (by simp [Noun.slot]))) ?_
      have hrec := subc_spec p (b - (y + 1)) 0 (y + 1) b ctx rfl (by omega)
      have hval : 0 + (b - (y + 1)) = (x + (b - y)) % p := by
        rw [show x + (b - y) = p + (b - (y + 1)) by omega, Nat.add_mod_left,
          Nat.mod_eq_of_lt (by omega)]
        omega
      rw [← hval]
      refine EvalsTo.call (L := LIB p) (sv := .cell (.atom 0) (.cell (.atom (y + 1)) (.atom b)))
        (cv := ctx) (by simp [Noun.slot]) ?_ (EvalsTo.slot (by simp [Noun.slot])) (slot_subc p _) hrec
      exact EvalsTo.cons (EvalsTo.quote _ _)
        (EvalsTo.cons (EvalsTo.op4 (EvalsTo.slot (by simp [Noun.slot])))
          (EvalsTo.slot (by simp [Noun.slot])))
    · refine EvalsTo.op6f (EvalsTo.ite1 hxp (evEqConst 12 (by simp [Noun.slot]))) ?_
      have hrec := ih (x + 1) (y + 1) b ctx (by omega) (by omega) hb (by omega)
      rw [show x + (b - y) = x + 1 + (b - (y + 1)) by omega]
      refine EvalsTo.call (L := LIB p) (sv := .cell (.atom (x + 1)) (.cell (.atom (y + 1)) (.atom b)))
        (cv := ctx) (by simp [Noun.slot]) ?_ (EvalsTo.slot (by simp [Noun.slot])) (slot_fadl p _) hrec
      exact EvalsTo.cons (EvalsTo.op4 (EvalsTo.slot (by simp [Noun.slot])))
        (EvalsTo.cons (EvalsTo.op4 (EvalsTo.slot (by simp [Noun.slot])))
          (EvalsTo.slot (by simp [Noun.slot])))

/-- **`fadd`**: `fadl (a, 0, b) = (a + b) % p`. -/
theorem fadd_spec {p : ℕ} (hp : 0 < p) {x b : ℕ} (hx : x < p) (hb : b < p) (ctx : Noun) :
    EvalsTo (core p (.cell (.atom x) (.cell (.atom 0) (.atom b))) ctx) (fadlArm p)
      (.atom ((x + b) % p)) := by
  simpa using fadl_spec hp b x 0 b ctx (by omega) (by omega) hb hx

/-- **`fmll_spec`**: `fmll (acc, c, a, b) = (acc + a·(b − c)) % p` for `acc, a < p`, `c ≤ b`. -/
theorem fmll_spec {p : ℕ} (hp : 0 < p) :
    ∀ (m acc c a b : ℕ) (ctx : Noun), b - c = m → c ≤ b → acc < p → a < p →
      EvalsTo (core p (.cell (.atom acc) (.cell (.atom c) (.cell (.atom a) (.atom b)))) ctx) fmllArm
        (.atom ((acc + a * (b - c)) % p)) := by
  intro m
  induction m with
  | zero =>
    intro acc c a b ctx hm hcb hacc ha
    have hd : c = b := by omega
    unfold fmllArm
    refine EvalsTo.op6t (EvalsTo.ite0 hd (evEqTest 26 55 (by simp [Noun.slot]) (by simp [Noun.slot])))
      ?_
    rw [show (acc + a * (b - c)) % p = acc by
      rw [show b - c = 0 by omega, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hacc]]
    exact EvalsTo.slot (by simp [Noun.slot])
  | succ m ih =>
    intro acc c a b ctx hm hcb hacc ha
    have hd : ¬ c = b := by omega
    unfold fmllArm
    refine EvalsTo.op6f (EvalsTo.ite1 hd (evEqTest 26 55 (by simp [Noun.slot]) (by simp [Noun.slot])))
      ?_
    have hrec := ih ((acc + a) % p) (c + 1) a b ctx (by omega) (by omega) (Nat.mod_lt _ hp) ha
    have hval : ((acc + a) % p + a * (b - (c + 1))) % p = (acc + a * (b - c)) % p := by
      rw [Nat.mod_add_mod, show b - c = (b - (c + 1)) + 1 by omega, Nat.mul_succ]
      congr 1; ring
    rw [← hval]
    set X := core p (.cell (.atom acc) (.cell (.atom c) (.cell (.atom a) (.atom b)))) ctx
    have hadd : EvalsTo X (call 10 (.cell (op0 12) (.cell (op1 (A 0)) (op0 54))) (op0 7))
        (.atom ((acc + a) % p)) :=
      EvalsTo.call (L := LIB p) (sv := .cell (.atom acc) (.cell (.atom 0) (.atom a))) (cv := ctx)
        (by simp [X, Noun.slot]) (EvalsTo.cons (EvalsTo.slot (by simp [X, Noun.slot]))
          (EvalsTo.cons (EvalsTo.quote _ _) (EvalsTo.slot (by simp [X, Noun.slot]))))
        (EvalsTo.slot (by simp [X, Noun.slot])) (slot_fadl p _) (fadd_spec hp hacc ha ctx)
    refine EvalsTo.call (L := LIB p)
      (sv := .cell (.atom ((acc + a) % p)) (.cell (.atom (c + 1)) (.cell (.atom a) (.atom b))))
      (cv := ctx) (by simp [X, Noun.slot]) ?_ (EvalsTo.slot (by simp [X, Noun.slot])) (slot_fmll p _) hrec
    refine EvalsTo.cons hadd (EvalsTo.cons (EvalsTo.op4 (EvalsTo.slot (by simp [X, Noun.slot])))
      (EvalsTo.cons (EvalsTo.slot (by simp [X, Noun.slot])) (EvalsTo.slot (by simp [X, Noun.slot]))))

/-- **`fmul`**: `fmll (0, 0, a, b) = (a·b) % p`. -/
theorem fmul_spec {p : ℕ} (hp : 0 < p) {x y : ℕ} (hx : x < p) (ctx : Noun) :
    EvalsTo (core p (.cell (.atom 0) (.cell (.atom 0) (.cell (.atom x) (.atom y)))) ctx) fmllArm
      (.atom ((x * y) % p)) := by
  simpa using fmll_spec hp y 0 0 x y ctx (by omega) (by omega) hp hx

/-! ## §3.2 Expressions, guards -/

theorem EvalsTo.cons' {X F₁ F₂ v₁ v₂ : Noun} (hc : ∃ a b, F₁ = .cell a b) (h₁ : EvalsTo X F₁ v₁)
    (h₂ : EvalsTo X F₂ v₂) : EvalsTo X (.cell F₁ F₂) (.cell v₁ v₂) := by
  obtain ⟨a, b, rfl⟩ := hc
  exact EvalsTo.cons h₁ h₂

theorem cEx_cell {k : ℕ} (ax : Fin k → ℕ) (e : Ex k) : ∃ a b, cEx ax e = .cell a b := by
  cases e <;> exact ⟨_, _, rfl⟩

theorem shapeF_inv {p : ℕ} {v : Noun} (h : shapeOK p .F v = true) : ∃ x, v = .atom x ∧ x < p := by
  cases v with
  | atom x => exact ⟨x, rfl, by simpa [shapeOK] using h⟩
  | cell _ _ => simp [shapeOK] at h

theorem shapeL_succ_inv {ok : Noun → Bool} {k : ℕ} {w : Noun} (h : shapeL ok (k + 1) w = true) :
    ∃ hd tl, w = .cell hd tl ∧ ok hd = true ∧ shapeL ok k tl = true := by
  cases w with
  | atom _ => simp [shapeL] at h
  | cell hd tl =>
    simp only [shapeL, Bool.and_eq_true] at h
    exact ⟨hd, tl, rfl, h.1, h.2⟩

theorem shapeOK_L (p n : ℕ) (τ : Ty) (v : Noun) : shapeOK p (.L n τ) v = shapeL (shapeOK p τ) n v := by
  cases v <;> rfl

/-- `tail^j` walks a well-shaped list. -/
theorem tail_spec {p : ℕ} {X F v : Noun} {τ : Ty} (hF : EvalsTo X F v) :
    ∀ (j n : ℕ), j ≤ n → shapeOK p (.L n τ) v = true →
      EvalsTo X (tailF j F) (ntail j v) ∧ shapeOK p (.L (n - j) τ) (ntail j v) = true := by
  intro j
  induction j with
  | zero => intro n _ hv; exact ⟨hF, by simpa [ntail] using hv⟩
  | succ j ih =>
    intro n hj hv
    obtain ⟨h1, h2⟩ := ih n (by omega) hv
    rw [shapeOK_L, show n - j = (n - (j + 1)) + 1 by omega] at h2
    obtain ⟨hd, tl, hw, -, htl⟩ := shapeL_succ_inv h2
    have hnt : ntail (j + 1) v = tl := by simp [ntail, hw, ntl]
    rw [hnt]
    refine ⟨EvalsTo.op7 h1 (EvalsTo.slot (X := ntail j v) (ax := 3) (v := tl) (by rw [hw]; simp [Noun.slot])), ?_⟩
    rwa [shapeOK_L]

theorem var_spec {p k : ℕ} {ax : Fin k → ℕ} {s v : Noun} {i : Fin k}
    (hs : Noun.slot (ax i) s = some v) : EvalsTo (.cell (LIB p) s) (cEx ax (.var i)) v :=
  EvalsTo.op7 (EvalsTo.slot (by simp [Noun.slot])) (EvalsTo.slot hs)

/-- **`ev_spec`**: a well-typed expression on well-shaped arguments evaluates (on `σ = [LIB s]`)
to `ev`, and its value has the expression's shape. -/
theorem ev_spec {p : ℕ} (hp : 0 < p) {k : ℕ} {ax : Fin k → ℕ} {inTy : Fin k → Ty} {s : Noun}
    {a : Fin k → Noun} (hs : ∀ i, Noun.slot (ax i) s = some (a i))
    (ha : ∀ i, shapeOK p (inTy i) (a i) = true) {e : Ex k} {τ : Ty} (h : HasTy p inTy e τ) :
    EvalsTo (.cell (LIB p) s) (cEx ax e) (ev p a e) ∧ shapeOK p τ (ev p a e) = true := by
  induction h with
  | var i => exact ⟨var_spec (hs i), ha i⟩
  | const hc => exact ⟨EvalsTo.quote _ _, by simp [ev, shapeOK, hc]⟩
  | nil τ => exact ⟨EvalsTo.quote _ _, by simp [ev, shapeOK, shapeL]⟩
  | weakN _ ih => exact ⟨ih.1, by simp [shapeOK]⟩
  | @add e₁ e₂ _ _ ih₁ ih₂ =>
    obtain ⟨x, hx, hxp⟩ := shapeF_inv ih₁.2
    obtain ⟨y, hy, hyp⟩ := shapeF_inv ih₂.2
    have hev : ev p a (.add e₁ e₂) = .atom ((x + y) % p) := by simp [ev, hx, hy, atomVal]
    refine ⟨?_, by rw [hev]; simp [shapeOK, Nat.mod_lt _ hp]⟩
    rw [hev]
    refine EvalsTo.call (L := LIB p) (sv := .cell (.atom x) (.cell (.atom 0) (.atom y)))
      (cv := .cell (LIB p) s) (by simp [Noun.slot]) ?_ (EvalsTo.slot (by simp [Noun.slot]))
      (slot_fadl p _) (fadd_spec hp hxp hyp _)
    refine EvalsTo.cons' (cEx_cell ax e₁) (hx ▸ ih₁.1) ?_
    exact EvalsTo.cons (EvalsTo.quote _ (A 0)) (hy ▸ ih₂.1)
  | @mul e₁ e₂ _ _ ih₁ ih₂ =>
    obtain ⟨x, hx, hxp⟩ := shapeF_inv ih₁.2
    obtain ⟨y, hy, hyp⟩ := shapeF_inv ih₂.2
    have hev : ev p a (.mul e₁ e₂) = .atom ((x * y) % p) := by simp [ev, hx, hy, atomVal]
    refine ⟨?_, by rw [hev]; simp [shapeOK, Nat.mod_lt _ hp]⟩
    rw [hev]
    refine EvalsTo.call (L := LIB p)
      (sv := .cell (.atom 0) (.cell (.atom 0) (.cell (.atom x) (.atom y))))
      (cv := .cell (LIB p) s) (by simp [Noun.slot]) ?_ (EvalsTo.slot (by simp [Noun.slot]))
      (slot_fmll p _) (fmul_spec hp hxp _)
    refine EvalsTo.cons (EvalsTo.quote _ (A 0)) (EvalsTo.cons (EvalsTo.quote _ (A 0)) ?_)
    exact EvalsTo.cons' (cEx_cell ax e₁) (hx ▸ ih₁.1) (hy ▸ ih₂.1)
  | @nth j n τ e _ hj ih =>
    obtain ⟨h1, h2⟩ := tail_spec ih.1 j n (by omega) ih.2
    rw [shapeOK_L, show n - j = (n - j - 1) + 1 by omega] at h2
    obtain ⟨hd, tl, hw, hhd, -⟩ := shapeL_succ_inv h2
    have hev : ev p a (.nth j e) = hd := by simp [ev, hw, nhd]
    rw [hev]
    exact ⟨EvalsTo.op7 h1 (EvalsTo.slot (X := ntail j (ev p a e)) (ax := 2) (v := hd)
      (by rw [hw]; simp [Noun.slot])), hhd⟩
  | @pair e₁ e₂ n τ _ _ ih₁ ih₂ =>
    refine ⟨EvalsTo.cons' (cEx_cell ax e₁) ih₁.1 ih₂.1, ?_⟩
    simp only [ev, shapeOK_L, shapeL, Bool.and_eq_true]
    exact ⟨ih₁.2, by rw [← shapeOK_L]; exact ih₂.2⟩

/-- **`guard_spec`**: `G τ f` returns `0` iff the value of `f` has shape `τ`, else `1` (on any
subject whose axis 2 is the library). -/
theorem guard_spec {p : ℕ} (hp : 0 < p) {X : Noun} (hX : Noun.slot 2 X = some (LIB p)) :
    ∀ (τ : Ty) (F v : Noun), (∃ a b, F = .cell a b) → EvalsTo X F v →
      EvalsTo X (gTy p τ F) (.atom (if shapeOK p τ v = true then 0 else 1)) := by
  intro τ
  induction τ with
  | F =>
    intro F v hc hF
    cases v with
    | cell x y =>
      simp only [gTy, shapeOK]
      exact EvalsTo.op6t (EvalsTo.op3 hF) (EvalsTo.quote _ _)
    | atom n =>
      simp only [gTy]
      have hisf := isf_spec hp (p - 1 - 0) 0 n X rfl (by omega)
      have heq : (if 0 ≤ n ∧ n < p then 0 else 1) = (if shapeOK p .F (.atom n) = true then 0 else 1) := by
        simp [shapeOK]
      rw [heq] at hisf
      obtain ⟨a, b, rfl⟩ := hc
      refine EvalsTo.op6f (EvalsTo.op3 hF) ?_
      exact EvalsTo.call (L := LIB p) (sv := .cell (.atom n) (.atom 0)) (cv := X) hX
        (EvalsTo.cons hF (EvalsTo.quote _ (A 0))) (EvalsTo.slot (by simp [Noun.slot]))
        (slot_isf p _) hisf
  | N =>
    intro F v hc hF
    simp only [gTy, shapeOK, if_true]
    cases v with
    | cell x y => exact EvalsTo.op6t (EvalsTo.op3 hF) (EvalsTo.quote _ _)
    | atom n => exact EvalsTo.op6f (EvalsTo.op3 hF) (EvalsTo.quote _ _)
  | L n τ ihτ =>
    simp only [gTy]
    induction n with
    | zero =>
      intro F v _ hF
      have := EvalsTo.op5 hF (EvalsTo.quote X (A 0))
      by_cases hv : v = .atom 0
      · subst hv; simpa [gL, tis, A, shapeOK_L, shapeL] using this
      · simpa [gL, tis, A, hv, shapeOK_L, shapeL] using this
    | succ n ihn =>
      intro F v hc hF
      cases v with
      | atom m =>
        simp only [gL, shapeOK_L, shapeL]
        exact EvalsTo.op6f (EvalsTo.op3 hF) (EvalsTo.quote _ _)
      | cell hd tl =>
        simp only [gL]
        refine EvalsTo.op6t (EvalsTo.op3 hF) ?_
        have hh := ihτ (op7 F (op0 2)) hd ⟨_, _, rfl⟩ (EvalsTo.op7 hF (EvalsTo.slot (by simp [Noun.slot])))
        have ht := ihn (op7 F (op0 3)) tl ⟨_, _, rfl⟩ (EvalsTo.op7 hF (EvalsTo.slot (by simp [Noun.slot])))
        by_cases hok : shapeOK p τ hd = true
        · rw [if_pos hok] at hh
          refine EvalsTo.op6t hh ?_
          simpa [shapeOK_L, shapeL, hok] using ht
        · rw [if_neg hok] at hh
          refine EvalsTo.op6f hh ?_
          simpa [A, shapeOK_L, shapeL, hok] using EvalsTo.quote X (A 1)

/-- **The argument guard**: on present arguments it returns `0` iff every argument is well shaped. -/
theorem guardAll_spec {p : ℕ} (hp : 0 < p) (T : Tpl) {s : Noun} {a : Fin T.k → Noun} :
    ∀ l : List (Fin T.k), (∀ i ∈ l, Noun.slot (T.ax i) s = some (a i)) →
      EvalsTo (.cell (LIB p) s) (guardAll p T l)
        (.atom (if l.all (fun i => shapeOK p (T.inTy i) (a i)) = true then 0 else 1)) := by
  intro l
  induction l with
  | nil => intro _; simpa [A, guardAll] using EvalsTo.quote (.cell (LIB p) s) (A 0)
  | cons i l ih =>
    intro hs
    have hg := guard_spec hp (X := .cell (LIB p) s) (by simp [Noun.slot]) (T.inTy i)
      (cEx T.ax (.var i)) (a i) ⟨_, _, rfl⟩ (var_spec (hs i (by simp)))
    cases l with
    | nil => simpa [guardAll] using hg
    | cons j l =>
      simp only [guardAll]
      by_cases hok : shapeOK p (T.inTy i) (a i) = true
      · rw [if_pos hok] at hg
        refine EvalsTo.op6t hg ?_
        simpa [hok] using ih (fun j hj => hs j (by simp [hj]))
      · rw [if_neg hok] at hg
        refine EvalsTo.op6f hg ?_
        simpa [A, hok] using EvalsTo.quote (.cell (LIB p) s) (A 1)

/-! ## §3.3 Shell inversions (op 0/1/3/5/6/7/8 only; never an arithmetic arm) -/

theorem inv_op0 {X w : Noun} {ax : ℕ} (h : EvalsTo X (op0 ax) w) : Noun.slot ax X = some w := by
  obtain ⟨f, h⟩ := h
  rcases f with _ | f
  · simp [evalN] at h
  · simpa [op0, evalN] using h

theorem inv_op1 {X c w : Noun} (h : EvalsTo X (op1 c) w) : w = c := by
  obtain ⟨f, h⟩ := h
  rcases f with _ | f
  · simp [evalN] at h
  · simp [op1, evalN] at h; exact h.symm

theorem inv_op3 {X F w : Noun} (h : EvalsTo X (op3 F) w) : ∃ v, EvalsTo X F v := by
  obtain ⟨f, h⟩ := h
  rcases f with _ | f
  · simp [evalN] at h
  · simp only [op3, evalN, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, -⟩ := h
    exact ⟨v, f, hv⟩

theorem inv_op5 {X F G w : Noun} (h : EvalsTo X (op5 F G) w) : ∃ v, EvalsTo X F v := by
  obtain ⟨f, h⟩ := h
  rcases f with _ | f
  · simp [evalN] at h
  · simp only [op5, evalN] at h
    cases hF : evalN f X F with
    | none => simp [hF] at h
    | some v => exact ⟨v, f, hF⟩

theorem inv_op6 {X B C D w : Noun} (h : EvalsTo X (op6 B C D) w) :
    (EvalsTo X B (.atom 0) ∧ EvalsTo X C w) ∨ (EvalsTo X B (.atom 1) ∧ EvalsTo X D w) := by
  obtain ⟨f, h⟩ := h
  rcases f with _ | f
  · simp [evalN] at h
  · simp only [op6, evalN] at h
    cases hB : evalN f X B with
    | none => simp [hB] at h
    | some b =>
      rw [hB] at h
      rcases b with ((_ | _ | n) | ⟨x, y⟩)
      · exact Or.inl ⟨⟨f, hB⟩, ⟨f, h⟩⟩
      · exact Or.inr ⟨⟨f, hB⟩, ⟨f, h⟩⟩
      · simp at h
      · simp at h

theorem inv_op7 {X F G w : Noun} (h : EvalsTo X (op7 F G) w) :
    ∃ v, EvalsTo X F v ∧ EvalsTo v G w := by
  obtain ⟨f, h⟩ := h
  rcases f with _ | f
  · simp [evalN] at h
  · simp only [op7, evalN] at h
    cases hF : evalN f X F with
    | none => simp [hF] at h
    | some v => rw [hF] at h; exact ⟨v, ⟨f, hF⟩, ⟨f, h⟩⟩

theorem inv_op8 {X F G w : Noun} (h : EvalsTo X (op8 F G) w) :
    ∃ v, EvalsTo X F v ∧ EvalsTo (.cell v X) G w := by
  obtain ⟨f, h⟩ := h
  rcases f with _ | f
  · simp [evalN] at h
  · simp only [op8, evalN] at h
    cases hF : evalN f X F with
    | none => simp [hF] at h
    | some v => rw [hF] at h; exact ⟨v, ⟨f, hF⟩, ⟨f, h⟩⟩

/-- A guard that returns anything has evaluated its operand (its FIRST read). -/
theorem gTy_reads {p : ℕ} {X : Noun} (τ : Ty) (F w : Noun) (h : EvalsTo X (gTy p τ F) w) :
    ∃ v, EvalsTo X F v := by
  cases τ with
  | F =>
    simp only [gTy] at h
    rcases inv_op6 h with ⟨hb, -⟩ | ⟨hb, -⟩ <;> exact inv_op3 hb
  | N =>
    simp only [gTy] at h
    rcases inv_op6 h with ⟨hb, -⟩ | ⟨hb, -⟩ <;> exact inv_op3 hb
  | L n τ =>
    cases n with
    | zero => simp only [gTy, gL] at h; exact inv_op5 h
    | succ n =>
      simp only [gTy, gL] at h
      rcases inv_op6 h with ⟨hb, -⟩ | ⟨hb, -⟩ <;> exact inv_op3 hb

/-- A guard chain that returns `0` read every argument slot. -/
theorem guardAll_reads {p : ℕ} (T : Tpl) {s : Noun} :
    ∀ l : List (Fin T.k), EvalsTo (.cell (LIB p) s) (guardAll p T l) (.atom 0) →
      ∀ i ∈ l, ∃ v, Noun.slot (T.ax i) s = some v := by
  intro l
  induction l with
  | nil => intro _ i hi; simp at hi
  | cons i l ih =>
    intro h j hj
    have hvar : ∀ w, EvalsTo (.cell (LIB p) s) (gTy p (T.inTy i) (cEx T.ax (.var i))) w →
        ∃ v, Noun.slot (T.ax i) s = some v := by
      intro w hg
      obtain ⟨v, hv⟩ := gTy_reads _ _ _ hg
      obtain ⟨w, hw3, hwa⟩ := inv_op7 hv
      have h3 := inv_op0 hw3
      simp [Noun.slot] at h3
      subst h3
      exact ⟨v, inv_op0 hwa⟩
    cases l with
    | nil =>
      simp only [guardAll] at h
      rcases List.mem_singleton.1 hj with rfl
      exact hvar _ h
    | cons k l =>
      simp only [guardAll] at h
      rcases inv_op6 h with ⟨hg, hrest⟩ | ⟨_, h1⟩
      · rcases List.mem_cons.1 hj with rfl | hj
        · exact hvar _ hg
        · exact ih hrest j hj
      · have := inv_op1 h1; simp [A] at this

/-! ## §3.4 The generic theorem -/

theorem sem_eq_some_iff {p : ℕ} {T : Tpl} {s r : Noun} :
    T.sem p s = some r ↔ ∃ a : Fin T.k → Noun, (∀ i, Noun.slot (T.ax i) s = some (a i)) ∧
      (∀ i, shapeOK p (T.inTy i) (a i) = true) ∧ ev p a T.body = r := by
  have := Template.rel_iff (T := T.toTemplate p) (s := s) (r := r)
  unfold Template.rel at this
  unfold Tpl.sem
  rw [this]
  constructor
  · rintro ⟨a, hs, hsem⟩
    simp only [Tpl.toTemplate] at hsem
    split_ifs at hsem with hok
    · exact ⟨a, hs, hok, Option.some.inj hsem⟩
  · rintro ⟨a, hs, hok, rfl⟩
    exact ⟨a, hs, by simp [Tpl.toTemplate, hok]⟩

theorem all_finRange_iff {k : ℕ} (P : Fin k → Bool) :
    (List.finRange k).all P = true ↔ ∀ i, P i = true := by
  simp [List.all_eq_true]

/-- **`compile_faithful`: the compiled formula realises every instance of the template.**
For a well-typed template `T` over a positive modulus `p`, if `T.sem p s = some r` (the template accepts the
subject `s` and returns `r`), then for some fuel, `evalN fuel s (compile p T) = some r`. -/
theorem compile_faithful {p : ℕ} (hp : 0 < p) (T : Tpl) (hT : T.WellTyped p) (s r : Noun)
    (h : T.sem p s = some r) : ∃ fuel, evalN fuel s (compile p T) = some r := by
  obtain ⟨a, hs, hok, rfl⟩ := sem_eq_some_iff.1 h
  have hg := guardAll_spec hp T (a := a) (List.finRange T.k) (fun i _ => hs i)
  rw [if_pos ((all_finRange_iff _).2 hok)] at hg
  exact EvalsTo.op8 (EvalsTo.quote s (LIB p)) (EvalsTo.op6t hg (ev_spec hp hs hok hT).1)

/-- **`compile_complete`: the compiled formula computes nothing beyond the template.**
For a well-typed template `T` over a positive modulus `p`, if `evalN fuel s (compile p T) = some r` for any
fuel, then `T.sem p s = some r`: every successful run of the compiled formula is an instance of the template. -/
theorem compile_complete {p : ℕ} (hp : 0 < p) (T : Tpl) (hT : T.WellTyped p) (fuel : ℕ)
    (s r : Noun) (h : evalN fuel s (compile p T) = some r) : T.sem p s = some r := by
  obtain ⟨v, hq, hb⟩ := inv_op8 (X := s) ⟨fuel, h⟩
  have hv := inv_op1 hq
  subst hv
  rcases inv_op6 hb with ⟨hg, hbody⟩ | ⟨_, hz⟩
  · have hreads := guardAll_reads T _ hg
    choose a hs using fun i => hreads i (List.mem_finRange i)
    have hg' := guardAll_spec hp T (a := a) (List.finRange T.k) (fun i _ => hs i)
    have hall : (List.finRange T.k).all (fun i => shapeOK p (T.inTy i) (a i)) = true := by
      by_contra hne
      rw [if_neg hne] at hg'
      have := EvalsTo.det hg hg'
      simp at this
    have hok := (all_finRange_iff _).1 hall
    have hr := EvalsTo.det hbody (ev_spec hp hs hok hT).1
    exact sem_eq_some_iff.2 ⟨a, hs, hok, hr.symm⟩
  · have := inv_op0 hz
    simp [Noun.slot] at this

/-- **`compile_crash_exact`**: off the template's domain the compiled formula never returns. -/
theorem compile_crash_exact {p : ℕ} (hp : 0 < p) (T : Tpl) (hT : T.WellTyped p) (s : Noun)
    (h : T.sem p s = none) : ∀ fuel, evalN fuel s (compile p T) = none := by
  intro fuel
  cases hc : evalN fuel s (compile p T) with
  | none => rfl
  | some r =>
    have := compile_complete hp T hT fuel s r hc
    rw [h] at this
    cases this

/-- **`compile_jetSpec_faithful`: a compiled well-typed template is a faithful jet specification.**
For a well-typed template `T` over a positive modulus `p`, the pair of the template's relation and the compiled
formula `compile p T` is a `JetSpec` satisfying `Faithful`: the relation holds exactly when the formula evaluates
to the result (`compile_faithful` and `compile_complete`). -/
theorem compile_jetSpec_faithful {p : ℕ} (hp : 0 < p) (T : Tpl) (hT : T.WellTyped p) :
    (⟨T.toTemplate p, compile p T⟩ : JetSpec).Faithful :=
  ⟨fun s r h => compile_faithful hp T hT s r h,
   fun s fuel r h => compile_complete hp T hT fuel s r h⟩

/-- The same, as J-1's pointwise form: `rel ↔ HoldsN` of the compiled formula. -/
theorem compile_rel_iff_holdsN {p : ℕ} (hp : 0 < p) (T : Tpl) (hT : T.WellTyped p) (s r : Noun) :
    (T.toTemplate p).rel s r ↔ HoldsN ⟨s, compile p T, r⟩ :=
  (JetSpec.faithful_iff _).1 (compile_jetSpec_faithful hp T hT) s r

end Nock.Jet.Autogen
