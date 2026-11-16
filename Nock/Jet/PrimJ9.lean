/-
  Nock/Jet/PrimJ9.lean

  **Primitive jet specs `add sub lt dec` and their faithfulness.**

  * `PrimOp`, `primSem : PrimOp → ℕ → ℕ → Option ℕ` (`dec` ignores its 2nd argument),
    `primTemplate op : Template` (binary ops: `k = 2`, `ax = ![2, 3]`; `dec` is UNARY: `k = 1`, `ax = ![1]`;
    `none` on a cell argument), `primC op : Noun` a naive Nock formula built from single-arm cores
    (`[ARM [S ctx]]`, recursion `[9 2 [[0 2] [S' [0 7]]]]`), `primSpec op : JetSpec`.
  * **`lt` loobean convention (read by `AluSZChipJ9`/`AluSZOps`):** `primSem lt a b = some 0 ↔ a < b`, and `some 1 ↔ b ≤ a`
    (Nock loobean: `0` = yes).  `sub a b` is `none` (crash) iff `a < b`.  `dec a` is `none` iff `a = 0`.
  * Proved for ALL seven ops (no side hypothesis): `primC_spec2`/`primC_spec_dec`, `primSpec_faithful`,
    `primSpec_complete`.  `mul` by counter induction on `b − i` (`mulArm_spec`, step via `addBody_spec`);
    `div`/`mod` by strong induction on `r` (`divLoop_spec`; test `ltBody_spec`, step `subBody_spec`);
    `b = 0` crashes in `guardNZ`.
-/
import Nock.Jet.Semantics
import Nock.Jet.Autogen
import Nock.Jet.VerifiedRegistry

set_option autoImplicit false

namespace Nock.Jet.Prim

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen

/-! ## §1 The operations and their semantics -/

inductive PrimOp | add | sub | lt | dec | mul | div | mod
  deriving DecidableEq

/-- Pure semantics on naturals. -/
def primSem : PrimOp → ℕ → ℕ → Option ℕ
  | .add, a, b => some (a + b)
  | .sub, a, b => if b ≤ a then some (a - b) else none
  | .lt, a, b => some (if a < b then 0 else 1)
  | .dec, a, _ => if 0 < a then some (a - 1) else none
  | .mul, a, b => some (a * b)
  | .div, a, b => if 0 < b then some (a / b) else none
  | .mod, a, b => if 0 < b then some (a % b) else none

/-! ## §2 Templates -/

def binT (op : PrimOp) : Template where
  k := 2
  ax := ![2, 3]
  sem a := match a 0, a 1 with
    | .atom x, .atom y => (primSem op x y).map Noun.atom
    | _, _ => none

def decT : Template where
  k := 1
  ax := ![1]
  sem a := match a 0 with
    | .atom x => (primSem .dec x 0).map Noun.atom
    | _ => none

def primTemplate : PrimOp → Template
  | .dec => decT
  | op => binT op

/-! ## §3 The formulas -/

/-- Build the core `[ARM [S0 s]]` on subject `s`, run its arm 2 against it. -/
def coreB (arm S0 : Noun) : Noun :=
  op7 (.cell (op1 arm) (.cell S0 (op0 1))) (op9 2 (op0 1))

def A0 : Noun := op1 (A 0)

/-- Counting loop `S = [x y]` (axes 12, 13): `x + (t − y)` by counting `y` up to `t` (the atom at axis `tax`). -/
def countArm (tax : ℕ) : Noun :=
  op6 (op5 (op0 13) (op0 tax)) (op0 12)
    (call 2 (.cell (op4 (op0 12)) (op4 (op0 13))) (op0 7))

/-- `lt` loop `S = [i _]`: `0` if `a < b` else `1` (test `b` first). -/
def ltArm : Noun :=
  op6 (op5 (op0 12) (op0 15)) (op1 (A 1))
    (op6 (op5 (op0 12) (op0 14)) (op1 (A 0))
      (call 2 (.cell (op4 (op0 12)) A0) (op0 7)))

/-- Bodies, on subject `[a b]` (dec: subject `a`). -/
def addBody : Noun := coreB (countArm 15) (.cell (op0 2) A0)
def subBody : Noun := coreB (countArm 14) (.cell A0 (op0 3))
def ltBody : Noun := coreB ltArm (.cell A0 A0)
def decBody : Noun := coreB (countArm 7) (.cell A0 (op1 (A 1)))

def crashF : Noun := op0 0

/-- Atom guard for a binary op: crash unless the subject is `[atom atom]`. -/
def guard2 (body : Noun) : Noun :=
  op6 (op3 (op0 2)) crashF (op6 (op3 (op0 3)) crashF body)

def decC : Noun :=
  op6 (op3 (op0 1)) crashF (op6 (op5 (op0 1) A0) crashF decBody)

/-! ### `mul`, `div`, `mod` arms -/

/-- `mul`: `S = [acc i]`, result `acc + a·(b − i)`; `acc + a` by `addBody` on `[acc a]`. -/
def mulArm : Noun :=
  op6 (op5 (op0 13) (op0 15)) (op0 12)
    (call 2 (.cell (op7 (.cell (op0 12) (op0 14)) addBody) (op4 (op0 13))) (op0 7))

/-- `div`/`mod`: `S = [q r]`, start `[0 a]`; while `¬ r < b`: `q+1`, `r − b` (by `subBody` on `[r b]`). -/
def divLoop (res : Noun) : Noun :=
  op6 (op7 (.cell (op0 13) (op0 15)) ltBody) res
    (call 2 (.cell (op4 (op0 12)) (op7 (.cell (op0 13) (op0 15)) subBody)) (op0 7))
def divArm : Noun := divLoop (op0 12)
def modArm : Noun := divLoop (op0 13)

def mulBody : Noun := coreB mulArm (.cell A0 A0)
def divBody : Noun := coreB divArm (.cell A0 (op0 2))
def modBody : Noun := coreB modArm (.cell A0 (op0 2))

/-- Guard `b ≠ 0` (axis 3). -/
def guardNZ (body : Noun) : Noun := op6 (op5 (op0 3) A0) crashF body

def primC : PrimOp → Noun
  | .add => guard2 addBody
  | .sub => guard2 (op6 ltBody crashF subBody)
  | .lt => guard2 ltBody
  | .dec => decC
  | .mul => guard2 mulBody
  | .div => guard2 (guardNZ divBody)
  | .mod => guard2 (guardNZ modBody)

def primSpec (op : PrimOp) : JetSpec := ⟨primTemplate op, primC op⟩

/-! ## §4 Loop specs (counter inductions) -/

theorem countArm_spec (tax : ℕ) (ctx : Noun) (t : ℕ)
    (hc : ∀ L S : Noun, Noun.slot tax (.cell L (.cell S ctx)) = some (.atom t)) :
    ∀ (m x y : ℕ), t - y = m → y ≤ t →
      EvalsTo (.cell (countArm tax) (.cell (.cell (.atom x) (.atom y)) ctx)) (countArm tax)
        (.atom (x + (t - y))) := by
  intro m
  induction m with
  | zero =>
    intro x y hm hy
    have hd : y = t := by omega
    unfold countArm
    refine EvalsTo.op6t (EvalsTo.ite0 hd (evEqTest 13 tax (by simp [Noun.slot]) (hc _ _))) ?_
    rw [show x + (t - y) = x by omega]
    exact EvalsTo.slot (by simp [Noun.slot])
  | succ m ih =>
    intro x y hm hy
    have hd : ¬ y = t := by omega
    have hrec := ih (x + 1) (y + 1) (by omega) (by omega)
    rw [show x + (t - y) = x + 1 + (t - (y + 1)) by omega]
    conv => rhs; unfold countArm
    refine EvalsTo.op6f (EvalsTo.ite1 hd (evEqTest 13 tax (by simp [Noun.slot]) (hc _ _))) ?_
    refine EvalsTo.call (L := countArm tax) (sv := .cell (.atom (x + 1)) (.atom (y + 1))) (cv := ctx)
      (by simp [Noun.slot]) ?_ (EvalsTo.slot (by simp [Noun.slot])) (by simp [Noun.slot]) hrec
    exact EvalsTo.cons (EvalsTo.op4 (EvalsTo.slot (by simp [Noun.slot])))
      (EvalsTo.op4 (EvalsTo.slot (by simp [Noun.slot])))

theorem ltArm_spec (a b : ℕ) :
    ∀ (m i : ℕ), min a b - i = m → i ≤ a → i ≤ b →
      EvalsTo (.cell ltArm (.cell (.cell (.atom i) (.atom 0)) (.cell (.atom a) (.atom b)))) ltArm
        (.atom (if a < b then 0 else 1)) := by
  intro m
  induction m with
  | zero =>
    intro i hm ha hb
    have hmin : i = min a b := by omega
    by_cases hib : i = b
    · unfold ltArm
      refine EvalsTo.op6t (EvalsTo.ite0 hib (evEqTest 12 15 (by simp [Noun.slot]) (by simp [Noun.slot]))) ?_
      rw [if_neg (by omega)]
      exact EvalsTo.quote _ _
    · have hia : i = a := by omega
      have hab : a < b := by omega
      unfold ltArm
      refine EvalsTo.op6f (EvalsTo.ite1 hib (evEqTest 12 15 (by simp [Noun.slot]) (by simp [Noun.slot])))
        (EvalsTo.op6t (EvalsTo.ite0 hia (evEqTest 12 14 (by simp [Noun.slot]) (by simp [Noun.slot]))) ?_)
      rw [if_pos hab]
      exact EvalsTo.quote _ _
  | succ m ih =>
    intro i hm ha hb
    have hib : ¬ i = b := by omega
    have hia : ¬ i = a := by omega
    have hrec := ih (i + 1) (by omega) (by omega) (by omega)
    conv => rhs; unfold ltArm
    refine EvalsTo.op6f (EvalsTo.ite1 hib (evEqTest 12 15 (by simp [Noun.slot]) (by simp [Noun.slot])))
      (EvalsTo.op6f (EvalsTo.ite1 hia (evEqTest 12 14 (by simp [Noun.slot]) (by simp [Noun.slot]))) ?_)
    refine EvalsTo.call (L := ltArm) (sv := .cell (.atom (i + 1)) (.atom 0)) (cv := .cell (.atom a) (.atom b))
      (by simp [Noun.slot]) ?_ (EvalsTo.slot (by simp [Noun.slot])) (by simp [Noun.slot]) hrec
    exact EvalsTo.cons (EvalsTo.op4 (EvalsTo.slot (by simp [Noun.slot]))) (EvalsTo.quote _ _)

/-! ## §5 Bodies -/

theorem coreB_spec {s S0 sv w : Noun} (arm : Noun) (hc : ∃ a b, S0 = .cell a b) (h0 : EvalsTo s S0 sv)
    (h : EvalsTo (.cell arm (.cell sv s)) arm w) : EvalsTo s (coreB arm S0) w := by
  unfold coreB
  refine EvalsTo.op7 (v := .cell arm (.cell sv s)) ?_ ?_
  · exact EvalsTo.cons (EvalsTo.quote _ _) (EvalsTo.cons' hc h0 (EvalsTo.slot (v := s) (by rw [Noun.slot])))
  · exact EvalsTo.op9 (EvalsTo.slot (by simp [Noun.slot])) (by simp [Noun.slot]) h

theorem addBody_spec (a b : ℕ) :
    EvalsTo (.cell (.atom a) (.atom b)) addBody (.atom (a + b)) := by
  have := countArm_spec 15 (.cell (.atom a) (.atom b)) b (by intro L S; simp [Noun.slot]) b a 0 (by omega)
    (by omega)
  rw [show a + b = a + (b - 0) by omega]
  exact coreB_spec _ ⟨_, _, rfl⟩ (sv := .cell (.atom a) (.atom 0))
    (EvalsTo.cons (EvalsTo.slot (by simp [Noun.slot])) (EvalsTo.quote _ _)) (by simpa using this)

theorem subBody_spec (a b : ℕ) (h : b ≤ a) :
    EvalsTo (.cell (.atom a) (.atom b)) subBody (.atom (a - b)) := by
  have := countArm_spec 14 (.cell (.atom a) (.atom b)) a (by intro L S; simp [Noun.slot]) (a - b) 0 b rfl h
  rw [show a - b = 0 + (a - b) by omega]
  exact coreB_spec _ ⟨_, _, rfl⟩ (sv := .cell (.atom 0) (.atom b))
    (EvalsTo.cons (EvalsTo.quote _ _) (EvalsTo.slot (by simp [Noun.slot]))) this

theorem ltBody_spec (a b : ℕ) :
    EvalsTo (.cell (.atom a) (.atom b)) ltBody (.atom (if a < b then 0 else 1)) := by
  have := ltArm_spec a b (min a b) 0 (by omega) (by omega) (by omega)
  exact coreB_spec _ ⟨_, _, rfl⟩ (sv := .cell (.atom 0) (.atom 0))
    (EvalsTo.cons (EvalsTo.quote _ _) (EvalsTo.quote _ _)) this

theorem decBody_spec (a : ℕ) (h : 0 < a) :
    EvalsTo (.atom a) decBody (.atom (a - 1)) := by
  have := countArm_spec 7 (.atom a) a (by intro L S; simp [Noun.slot]) (a - 1) 0 1 (by omega) (by omega)
  rw [show a - 1 = 0 + (a - 1) by omega]
  exact coreB_spec _ ⟨_, _, rfl⟩ (sv := .cell (.atom 0) (.atom 1))
    (EvalsTo.cons (EvalsTo.quote _ _) (EvalsTo.quote _ _)) (by simpa using this)


theorem mulArm_spec (a b : ℕ) :
    ∀ (m acc i : ℕ), b - i = m → i ≤ b →
      EvalsTo (.cell mulArm (.cell (.cell (.atom acc) (.atom i)) (.cell (.atom a) (.atom b)))) mulArm
        (.atom (acc + a * (b - i))) := by
  intro m
  induction m with
  | zero =>
    intro acc i hm hi
    have hd : i = b := by omega
    refine EvalsTo.op6t (EvalsTo.ite0 hd (evEqTest 13 15 (by simp [Noun.slot]) (by simp [Noun.slot]))) ?_
    rw [show a * (b - i) = 0 by rw [show b - i = 0 by omega]; exact Nat.mul_zero a, Nat.add_zero]
    exact EvalsTo.slot (by simp [Noun.slot])
  | succ m ih =>
    intro acc i hm hi
    have hd : ¬ i = b := by omega
    have hrec := ih (acc + a) (i + 1) (by omega) (by omega)
    have hv : acc + a * (b - i) = acc + a + a * (b - (i + 1)) := by
      rw [show b - i = (b - (i + 1)) + 1 by omega, Nat.mul_succ]; omega
    rw [hv]
    refine EvalsTo.op6f (EvalsTo.ite1 hd (evEqTest 13 15 (by simp [Noun.slot]) (by simp [Noun.slot]))) ?_
    refine EvalsTo.call (L := mulArm) (sv := .cell (.atom (acc + a)) (.atom (i + 1)))
      (cv := .cell (.atom a) (.atom b))
      (by simp [Noun.slot]) ?_ (EvalsTo.slot (by simp [Noun.slot])) (by simp [Noun.slot]) hrec
    refine EvalsTo.cons ?_ (EvalsTo.op4 (EvalsTo.slot (by simp [Noun.slot])))
    exact EvalsTo.op7 (v := .cell (.atom acc) (.atom a))
      (EvalsTo.cons (EvalsTo.slot (by simp [Noun.slot])) (EvalsTo.slot (by simp [Noun.slot])))
      (addBody_spec acc a)

theorem mulBody_spec (a b : ℕ) :
    EvalsTo (.cell (.atom a) (.atom b)) mulBody (.atom (a * b)) := by
  have := mulArm_spec a b b 0 0 (by omega) (by omega)
  rw [show a * b = 0 + a * (b - 0) by simp]
  exact coreB_spec _ ⟨_, _, rfl⟩ (sv := .cell (.atom 0) (.atom 0))
    (EvalsTo.cons (EvalsTo.quote _ _) (EvalsTo.quote _ _)) this

/-- Generic `div`/`mod` loop: strong induction on `r`. -/
theorem divLoop_spec (a b : ℕ) (hb : 0 < b) (res : Noun) (G : ℕ → ℕ → ℕ)
    (hbase : ∀ q r, r < b →
      EvalsTo (.cell (divLoop res) (.cell (.cell (.atom q) (.atom r)) (.cell (.atom a) (.atom b)))) res
        (.atom (G q r)))
    (hstep : ∀ q r, ¬ r < b → G q r = G (q + 1) (r - b)) :
    ∀ (r q : ℕ),
      EvalsTo (.cell (divLoop res) (.cell (.cell (.atom q) (.atom r)) (.cell (.atom a) (.atom b))))
        (divLoop res) (.atom (G q r)) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro q
    have hlt := ltBody_spec r b
    have htest : ∀ v, EvalsTo (.cell (.atom r) (.atom b)) ltBody v →
        EvalsTo (.cell (divLoop res) (.cell (.cell (.atom q) (.atom r)) (.cell (.atom a) (.atom b))))
          (op7 (.cell (op0 13) (op0 15)) ltBody) v := fun v hv =>
      EvalsTo.op7 (v := .cell (.atom r) (.atom b))
        (EvalsTo.cons (EvalsTo.slot (by simp [Noun.slot])) (EvalsTo.slot (by simp [Noun.slot]))) hv
    by_cases h : r < b
    · rw [if_pos h] at hlt
      exact EvalsTo.op6t (htest _ hlt) (hbase q r h)
    · rw [if_neg h] at hlt
      have hrec := ih (r - b) (by omega) (q + 1)
      rw [hstep q r h]
      refine EvalsTo.op6f (htest _ hlt) ?_
      refine EvalsTo.call (L := divLoop res) (sv := .cell (.atom (q + 1)) (.atom (r - b)))
        (cv := .cell (.atom a) (.atom b))
        (by simp [Noun.slot]) ?_ (EvalsTo.slot (by simp [Noun.slot])) (by simp [Noun.slot]) hrec
      refine EvalsTo.cons (EvalsTo.op4 (EvalsTo.slot (by simp [Noun.slot]))) ?_
      exact EvalsTo.op7 (v := .cell (.atom r) (.atom b))
        (EvalsTo.cons (EvalsTo.slot (by simp [Noun.slot])) (EvalsTo.slot (by simp [Noun.slot])))
        (subBody_spec r b (by omega))

theorem divBody_spec (a b : ℕ) (hb : 0 < b) :
    EvalsTo (.cell (.atom a) (.atom b)) divBody (.atom (a / b)) := by
  have := divLoop_spec a b hb (op0 12) (fun q r => q + r / b)
    (fun q r h => by
      rw [Nat.div_eq_of_lt h, Nat.add_zero]; exact EvalsTo.slot (by simp [Noun.slot]))
    (fun q r h => by
      have : r / b = (r - b) / b + 1 := by
        conv_lhs => rw [show r = (r - b) + b by omega]
        exact Nat.add_div_right _ hb
      rw [this]; omega) a 0
  rw [show a / b = 0 + a / b by simp]
  exact coreB_spec _ ⟨_, _, rfl⟩ (sv := .cell (.atom 0) (.atom a))
    (EvalsTo.cons (EvalsTo.quote _ _) (EvalsTo.slot (by simp [Noun.slot]))) this

theorem modBody_spec (a b : ℕ) (hb : 0 < b) :
    EvalsTo (.cell (.atom a) (.atom b)) modBody (.atom (a % b)) := by
  have := divLoop_spec a b hb (op0 13) (fun _ r => r % b)
    (fun q r h => by
      rw [Nat.mod_eq_of_lt h]; exact EvalsTo.slot (by simp [Noun.slot]))
    (fun q r h => by
      exact Nat.mod_eq_sub_mod (by omega)) a 0
  exact coreB_spec _ ⟨_, _, rfl⟩ (sv := .cell (.atom 0) (.atom a))
    (EvalsTo.cons (EvalsTo.quote _ _) (EvalsTo.slot (by simp [Noun.slot]))) this

/-! ## §6 Crash lemmas -/

def Crashes (X F : Noun) : Prop := ∀ f, evalN f X F = none

theorem crash_slot0 (X : Noun) : Crashes X crashF := by
  intro f; cases f <;> simp [crashF, op0, evalN, Noun.slot]

theorem crash_op3 {X f : Noun} (h : Crashes X f) : Crashes X (op3 f) := by
  intro n; cases n <;> simp [Autogen.op3, evalN, h _]

theorem crash_op6c {X b c d : Noun} (h₁ : EvalsTo X b (.atom 0)) (h₂ : Crashes X c) :
    Crashes X (op6 b c d) := by
  intro n
  obtain ⟨f₁, h₁⟩ := h₁
  cases n with
  | zero => simp [Autogen.op6, evalN]
  | succ n =>
    simp only [Autogen.op6, evalN]
    cases hb : evalN n X b with
    | none => rfl
    | some v =>
      have := evalN_deterministic h₁ hb
      subst this
      simp [h₂ n]

theorem crash_op6d {X b c d : Noun} (h₁ : EvalsTo X b (.atom 1)) (h₂ : Crashes X d) :
    Crashes X (op6 b c d) := by
  intro n
  obtain ⟨f₁, h₁⟩ := h₁
  cases n with
  | zero => simp [Autogen.op6, evalN]
  | succ n =>
    simp only [Autogen.op6, evalN]
    cases hb : evalN n X b with
    | none => rfl
    | some v =>
      have := evalN_deterministic h₁ hb
      subst this
      simp [h₂ n]

theorem crash_op6b {X b c d : Noun} (h : Crashes X b) : Crashes X (op6 b c d) := by
  intro n
  cases n with
  | zero => simp [Autogen.op6, evalN]
  | succ n => simp [Autogen.op6, evalN, h n]

theorem crash_slot_none {X : Noun} {ax : ℕ} (h : Noun.slot ax X = none) : Crashes X (op0 ax) := by
  intro n; cases n <;> simp [op0, evalN, h]

/-! ## §7 `primC_spec` and crash exactness -/

theorem guard2_spec (x y : ℕ) {body w : Noun}
    (h : EvalsTo (.cell (.atom x) (.atom y)) body w) :
    EvalsTo (.cell (.atom x) (.atom y)) (guard2 body) w := by
  unfold guard2
  refine EvalsTo.op6f ?_ (EvalsTo.op6f ?_ h)
  · simpa [Noun.wut] using EvalsTo.op3 (EvalsTo.slot (X := .cell (.atom x) (.atom y)) (ax := 2) (v := .atom x)
      (by simp [Noun.slot]))
  · simpa [Noun.wut] using EvalsTo.op3 (EvalsTo.slot (X := .cell (.atom x) (.atom y)) (ax := 3) (v := .atom y)
      (by simp [Noun.slot]))

theorem guard2_crash {s body : Noun} (h : ¬ ∃ x y : ℕ, s = .cell (.atom x) (.atom y)) :
    Crashes s (guard2 body) := by
  unfold guard2
  cases s with
  | atom n => exact crash_op6b (crash_op3 (crash_slot_none (by simp [Noun.slot])))
  | cell u v =>
    cases u with
    | cell u1 u2 =>
      exact crash_op6c (by simpa [Noun.wut] using EvalsTo.op3 (EvalsTo.slot (X := .cell (.cell u1 u2) v)
        (ax := 2) (v := .cell u1 u2) (by simp [Noun.slot]))) (crash_slot0 _)
    | atom x =>
      cases v with
      | atom y => exact absurd ⟨x, y, rfl⟩ h
      | cell v1 v2 =>
        refine crash_op6d (by simpa [Noun.wut] using EvalsTo.op3 (EvalsTo.slot (X := .cell (.atom x) (.cell v1 v2))
          (ax := 2) (v := .atom x) (by simp [Noun.slot]))) (crash_op6c ?_ (crash_slot0 _))
        simpa [Noun.wut] using EvalsTo.op3 (EvalsTo.slot (X := .cell (.atom x) (.cell v1 v2))
          (ax := 3) (v := .cell v1 v2) (by simp [Noun.slot]))

theorem guardNZ_test (x y : ℕ) :
    EvalsTo (.cell (.atom x) (.atom y)) (op5 (op0 3) A0) (.atom (if y = 0 then 0 else 1)) := by
  have := EvalsTo.op5 (EvalsTo.slot (X := .cell (.atom x) (.atom y)) (ax := 3) (v := .atom y)
    (by simp [Noun.slot])) (EvalsTo.quote (.cell (.atom x) (.atom y)) (A 0))
  rw [A, tis_atom] at this
  exact this

theorem guardNZ_spec (x y : ℕ) (hy : 0 < y) {body w : Noun}
    (h : EvalsTo (.cell (.atom x) (.atom y)) body w) :
    EvalsTo (.cell (.atom x) (.atom y)) (guardNZ body) w := by
  refine EvalsTo.op6f ?_ h
  have := guardNZ_test x y
  rwa [if_neg (by omega)] at this

theorem guard2_nz_crash (x : ℕ) (body : Noun) :
    Crashes (.cell (.atom x) (.atom 0)) (guard2 (guardNZ body)) := by
  unfold guard2
  refine crash_op6d ?_ (crash_op6d ?_ (crash_op6c ?_ (crash_slot0 _)))
  · simpa [Noun.wut] using EvalsTo.op3 (EvalsTo.slot (X := .cell (.atom x) (.atom 0)) (ax := 2) (v := .atom x)
      (by simp [Noun.slot]))
  · simpa [Noun.wut] using EvalsTo.op3 (EvalsTo.slot (X := .cell (.atom x) (.atom 0)) (ax := 3) (v := .atom 0)
      (by simp [Noun.slot]))
  · simpa using guardNZ_test x 0

/-- Positive direction on atoms, every op other than `dec`. -/
theorem primC_spec2 (op : PrimOp) (hd : op ≠ .dec) (x y r : ℕ)
    (h : primSem op x y = some r) :
    EvalsTo (.cell (.atom x) (.atom y)) (primC op) (.atom r) := by
  cases op with
  | add => obtain rfl := Option.some.inj h; exact guard2_spec x y (addBody_spec x y)
  | sub =>
    simp only [primSem] at h
    split_ifs at h with hb
    obtain rfl := Option.some.inj h
    refine guard2_spec x y (EvalsTo.op6f ?_ (subBody_spec x y hb))
    have := ltBody_spec x y
    rwa [if_neg (by omega)] at this
  | lt => obtain rfl := Option.some.inj h; exact guard2_spec x y (ltBody_spec x y)
  | dec => exact absurd rfl hd
  | mul => obtain rfl := Option.some.inj h; exact guard2_spec x y (mulBody_spec x y)
  | div =>
    simp only [primSem] at h
    split_ifs at h with hb
    obtain rfl := Option.some.inj h
    exact guard2_spec x y (guardNZ_spec x y hb (divBody_spec x y hb))
  | mod =>
    simp only [primSem] at h
    split_ifs at h with hb
    obtain rfl := Option.some.inj h
    exact guard2_spec x y (guardNZ_spec x y hb (modBody_spec x y hb))

theorem primC_spec_dec (x r : ℕ) (h : primSem .dec x 0 = some r) :
    EvalsTo (.atom x) (primC .dec) (.atom r) := by
  simp only [primSem] at h
  split_ifs at h with hx
  cases h
  simp only [primC, decC]
  refine EvalsTo.op6f ?_ (EvalsTo.op6f ?_ (decBody_spec x hx))
  · simpa [Noun.wut] using EvalsTo.op3 (EvalsTo.slot (X := .atom x) (ax := 1) (v := .atom x) (by simp [Noun.slot]))
  · have := EvalsTo.op5 (EvalsTo.slot (X := .atom x) (ax := 1) (v := .atom x) (by simp [Noun.slot]))
      (EvalsTo.quote (.atom x) (A 0))
    rw [A, tis_atom, if_neg (by omega)] at this
    exact this

/-- Crash on atoms where `primSem = none` (`sub a < b`). -/
theorem primC_crash_sub (x y : ℕ) (h : ¬ y ≤ x) : Crashes (.cell (.atom x) (.atom y)) (primC .sub) := by
  simp only [primC]
  unfold guard2
  refine crash_op6d ?_ (crash_op6d ?_ (crash_op6c ?_ (crash_slot0 _)))
  · simpa [Noun.wut] using EvalsTo.op3 (EvalsTo.slot (X := .cell (.atom x) (.atom y)) (ax := 2) (v := .atom x)
      (by simp [Noun.slot]))
  · simpa [Noun.wut] using EvalsTo.op3 (EvalsTo.slot (X := .cell (.atom x) (.atom y)) (ax := 3) (v := .atom y)
      (by simp [Noun.slot]))
  · have := ltBody_spec x y
    rwa [if_pos (by omega)] at this

theorem primC_crash_dec_zero : Crashes (.atom 0) (primC .dec) := by
  simp only [primC, decC]
  refine crash_op6d ?_ (crash_op6c ?_ (crash_slot0 _))
  · simpa [Noun.wut] using EvalsTo.op3 (EvalsTo.slot (X := .atom 0) (ax := 1) (v := .atom 0) (by simp [Noun.slot]))
  · have := EvalsTo.op5 (EvalsTo.slot (X := .atom 0) (ax := 1) (v := .atom 0) (by simp [Noun.slot]))
      (EvalsTo.quote (.atom 0) (A 0))
    rw [A, tis_atom, if_pos rfl] at this
    exact this

theorem primC_crash_dec_cell (u v : Noun) : Crashes (.cell u v) (primC .dec) := by
  simp only [primC, decC]
  refine crash_op6c ?_ (crash_slot0 _)
  simpa [Noun.wut] using EvalsTo.op3 (EvalsTo.slot (X := .cell u v) (ax := 1) (v := .cell u v) (by simp [Noun.slot]))

/-! ## §8 Templates: shape lemmas -/

theorem binT_rel {op : PrimOp} {s r : Noun} (h : (binT op).rel s r) :
    ∃ x y n, s = .cell (.atom x) (.atom y) ∧ primSem op x y = some n ∧ r = .atom n := by
  rw [Template.rel_iff] at h
  obtain ⟨a, ha, hs⟩ := h
  have h2 : Noun.slot 2 s = some (a ⟨0, Nat.zero_lt_two⟩) := by
    have := ha ⟨0, Nat.zero_lt_two⟩
    simpa [binT, Fin.zero_eta, Matrix.cons_val_zero] using this
  have h3 : Noun.slot 3 s = some (a ⟨1, Nat.one_lt_two⟩) := by
    have := ha ⟨1, Nat.one_lt_two⟩
    simpa [binT, Fin.mk_one, Matrix.cons_val_one] using this
  have hs' : (match a ⟨0, Nat.zero_lt_two⟩, a ⟨1, Nat.one_lt_two⟩ with
      | .atom x, .atom y => (primSem op x y).map Noun.atom
      | _, _ => none) = some r := hs
  obtain ⟨v, hv⟩ : ∃ v, a ⟨0, Nat.zero_lt_two⟩ = v := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, a ⟨1, Nat.one_lt_two⟩ = w := ⟨_, rfl⟩
  rw [hv] at h2 hs'
  rw [hw] at h3 hs'
  cases s with
  | atom n => simp [Noun.slot] at h2
  | cell u t =>
    simp [Noun.slot] at h2 h3
    subst h2; subst h3
    cases u with
    | cell _ _ => simp at hs'
    | atom x =>
      cases t with
      | cell _ _ => simp at hs'
      | atom y =>
        simp only [Option.map_eq_some_iff] at hs'
        obtain ⟨n, hn, hr⟩ := hs'
        exact ⟨x, y, n, rfl, hn, hr.symm⟩

theorem binT_rel_of {op : PrimOp} {x y n : ℕ} (h : primSem op x y = some n) :
    (binT op).rel (.cell (.atom x) (.atom y)) (.atom n) := by
  rw [Template.rel_iff]
  refine ⟨![.atom x, .atom y], ?_, ?_⟩
  · intro i; fin_cases i <;> simp [binT, Noun.slot]
  · simp [binT, h]

theorem decT_rel {s r : Noun} (h : decT.rel s r) :
    ∃ x n, s = .atom x ∧ primSem .dec x 0 = some n ∧ r = .atom n := by
  rw [Template.rel_iff] at h
  obtain ⟨a, ha, hs⟩ := h
  have h1 : Noun.slot 1 s = some (a ⟨0, by decide⟩) := by
    have := ha ⟨0, by decide⟩
    simpa [decT, Fin.zero_eta, Matrix.cons_val_zero] using this
  have hs' : (match a ⟨0, by decide⟩ with
      | .atom x => (primSem .dec x 0).map Noun.atom
      | _ => none) = some r := hs
  obtain ⟨v, hv⟩ : ∃ v, a ⟨0, by decide⟩ = v := ⟨_, rfl⟩
  rw [hv] at h1 hs'
  simp only [Noun.slot, Option.some.injEq] at h1
  subst h1
  cases s with
  | cell u w => simp at hs'
  | atom x =>
    simp only [Option.map_eq_some_iff] at hs'
    obtain ⟨n, hn, hr⟩ := hs'
    exact ⟨x, n, rfl, hn, hr.symm⟩

theorem decT_rel_of {x n : ℕ} (h : primSem .dec x 0 = some n) : decT.rel (.atom x) (.atom n) := by
  rw [Template.rel_iff]
  refine ⟨![.atom x], ?_, ?_⟩
  · intro i; fin_cases i; simp [decT, Noun.slot]
  · simp [decT, h]

/-! ## §9 Headline theorems -/

theorem primSpec_faithful (op : PrimOp) : (primSpec op).Faithful := by
  by_cases hd : op = .dec
  · subst hd
    refine ⟨?_, ?_⟩
    · intro s r h
      obtain ⟨x, n, rfl, hn, rfl⟩ := decT_rel (by simpa [primSpec, primTemplate] using h)
      exact primC_spec_dec x n hn
    · intro s fuel r h
      simp only [primSpec, primTemplate] at h ⊢
      cases s with
      | cell u v => rw [primC_crash_dec_cell u v fuel] at h; cases h
      | atom x =>
        by_cases hx : 0 < x
        · have hn : primSem .dec x 0 = some (x - 1) := by simp [primSem, hx]
          obtain ⟨f, hf⟩ := primC_spec_dec x _ hn
          have := evalN_deterministic h hf
          subst this
          exact decT_rel_of hn
        · have : x = 0 := by omega
          subst this
          rw [primC_crash_dec_zero fuel] at h; cases h
  · have hb : primTemplate op = binT op := by cases op <;> simp_all [primTemplate]
    refine ⟨?_, ?_⟩
    · intro s r h
      obtain ⟨x, y, n, rfl, hn, rfl⟩ := binT_rel (by simpa [primSpec, hb] using h)
      exact primC_spec2 op hd x y n hn
    · intro s fuel r h
      simp only [primSpec] at h ⊢
      rw [hb]
      by_cases hs : ∃ x y : ℕ, s = .cell (.atom x) (.atom y)
      · obtain ⟨x, y, rfl⟩ := hs
        cases hsem : primSem op x y with
        | none =>
          exfalso
          have hsub : (op = .sub ∧ ¬ y ≤ x) ∨ ((op = .div ∨ op = .mod) ∧ y = 0) := by
            cases op with
            | add => simp [primSem] at hsem
            | sub =>
              left; refine ⟨rfl, ?_⟩
              intro hle; simp [primSem, hle] at hsem
            | lt => simp [primSem] at hsem
            | dec => exact absurd rfl hd
            | mul => simp [primSem] at hsem
            | div =>
              right; refine ⟨Or.inl rfl, ?_⟩
              by_contra hy; simp [primSem, Nat.pos_of_ne_zero hy] at hsem
            | mod =>
              right; refine ⟨Or.inr rfl, ?_⟩
              by_contra hy; simp [primSem, Nat.pos_of_ne_zero hy] at hsem
          rcases hsub with ⟨rfl, hyx⟩ | ⟨hdm, rfl⟩
          · rw [primC_crash_sub x y hyx fuel] at h; cases h
          · rcases hdm with rfl | rfl
            · have hc : evalN fuel (.cell (.atom x) (.atom 0)) (primC .div) = none :=
                guard2_nz_crash x divBody fuel
              rw [hc] at h; cases h
            · have hc : evalN fuel (.cell (.atom x) (.atom 0)) (primC .mod) = none :=
                guard2_nz_crash x modBody fuel
              rw [hc] at h; cases h
        | some n =>
          obtain ⟨f, hf⟩ := primC_spec2 op hd x y n hsem
          have := evalN_deterministic h hf
          subst this
          exact binT_rel_of hsem
      · exfalso
        have hc : Crashes s (primC op) := by
          revert hd; cases op <;> intro hd <;> first | exact guard2_crash hs | exact absurd rfl hd
        rw [hc fuel] at h; cases h

theorem primSpec_complete (op : PrimOp) : Complete (primSpec op).T (primSpec op).c :=
  (primSpec_faithful op).2

/-- Register a proved primitive. -/
def _root_.Nock.Jet.VerifiedRegistry.addPrim (V : Nock.Jet.VerifiedRegistry) (n : ℕ) (op : PrimOp) :
    Nock.Jet.VerifiedRegistry :=
  V.add n (primSpec op) (primSpec_faithful op)

#print axioms primSpec_faithful
#print axioms primSpec_complete

end Nock.Jet.Prim
