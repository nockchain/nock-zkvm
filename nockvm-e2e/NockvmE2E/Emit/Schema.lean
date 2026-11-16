/-
  NockvmE2E/Emit/Schema.lean

  **The AIR-schema emitter, core.**  A deep embedding `JExpr` of the expression language of
  `nockvm-air-rs/SCHEMA.md` v1.1 (the Rust `nockvm_air::Expr`), an emitter from the Lean gate languages
  `CoeffExpr (ZMod p)` / `MixedExpr (ZMod p)` into it, a decoder back, and the kernel-checked round trip

      `decodeMixed (emitMixed e) = some (norm e)`,   `decodeBase (emitBase g) = some g`,

  where `norm` only (a) rewrites `Scale g u` to `Mul (Lift g) u` and (b) unrolls `Pow x n` to a product
  (the Rust schema has no `ext_scale` / `ext_pow`); `eval_norm` proves `norm` preserves `MixedExpr.eval`.
  Not proved here (and labelled so): `toJson` / the Rust parser (the JSON text itself), and the
  conventions of the Rust *checker* (see the notes in `NockvmE2E/Emit/Chips.lean`).
-/
import Nock.NockVMROM.Thm54.MixedCoordinateCompiler
import Nock.NockVMROM.Thm54.CoordinateRAPCore
import Nock.Field
import Lean.Data.Json

set_option autoImplicit false

namespace Nock.Emit

open Nock Nock.Reified Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.MixedCoordinateCompiler

/-- The base field of the J-8 checker, `ZMod p`, `p = 2^64 - 2^32 + 1`. -/
abbrev Gl := ZMod Nock.Field.p

instance : NeZero Nock.Field.p := ⟨by unfold Nock.Field.p; norm_num⟩

/-- The schema's expression trees (the Rust `Expr`).  Base forms first, then the 𝕂-valued ones. -/
inductive JExpr where
  | var (k : VarKind) (i : ℕ)
  | constF (n : ℕ)
  | constZ (z : ℤ)
  | add (a b : JExpr) | sub (a b : JExpr) | mul (a b : JExpr)
  | neg (a : JExpr)
  | pow (a : JExpr) (n : ℕ)
  | extVar (i : ℕ) (k : VarKind)
  | extChal (i : ℕ)
  | extLift (a : JExpr)
  | extAdd (a b : JExpr) | extSub (a b : JExpr) | extMul (a b : JExpr)
  | extNeg (a : JExpr)
  /-- (DAG documents) index into the chip's `shared` table; each entry only refers to earlier ones. -/
  | ref (i : ℕ)
deriving Repr, BEq

/-! ## Base-field expressions -/

def emitBase : CoeffExpr Gl → JExpr
  | .const c => .constF c.val
  | .var k i => .var k i
  | .add a b => .add (emitBase a) (emitBase b)
  | .sub a b => .sub (emitBase a) (emitBase b)
  | .mul a b => .mul (emitBase a) (emitBase b)
  | .neg a => .neg (emitBase a)
  | .pow a n => .pow (emitBase a) n

def decodeBase : JExpr → Option (CoeffExpr Gl)
  | .constF n => some (.const (n : Gl))
  | .var k i => some (.var k i)
  | .add a b => match decodeBase a, decodeBase b with | some x, some y => some (.add x y) | _, _ => none
  | .sub a b => match decodeBase a, decodeBase b with | some x, some y => some (.sub x y) | _, _ => none
  | .mul a b => match decodeBase a, decodeBase b with | some x, some y => some (.mul x y) | _, _ => none
  | .neg a => (decodeBase a).map .neg
  | .pow a n => (decodeBase a).map (.pow · n)
  | _ => none

theorem decodeBase_emitBase : ∀ g : CoeffExpr Gl, decodeBase (emitBase g) = some g
  | .const c => by simp [emitBase, decodeBase]
  | .var k i => rfl
  | .add a b => by simp [emitBase, decodeBase, decodeBase_emitBase a, decodeBase_emitBase b]
  | .sub a b => by simp [emitBase, decodeBase, decodeBase_emitBase a, decodeBase_emitBase b]
  | .mul a b => by simp [emitBase, decodeBase, decodeBase_emitBase a, decodeBase_emitBase b]
  | .neg a => by simp [emitBase, decodeBase, decodeBase_emitBase a]
  | .pow a n => by simp [emitBase, decodeBase, decodeBase_emitBase a]

/-! ## 𝕂-valued (mixed) expressions -/

/-- Unrolled power (`x^0 = 1`). -/
def powN {F : Type*} : MixedExpr F → ℕ → MixedExpr F
  | _, 0 => .Const 1
  | x, n + 1 => .Mul (powN x n) x

/-- Normal form: `Scale g u ↦ Mul (Lift g) u`, `Pow x n ↦ powN x n`. -/
def norm {F : Type*} : MixedExpr F → MixedExpr F
  | .Var k i => .Var k i
  | .Lift g => .Lift g
  | .Scale g u => .Mul (.Lift g) (norm u)
  | .Const c => .Const c
  | .Add x y => .Add (norm x) (norm y)
  | .Sub x y => .Sub (norm x) (norm y)
  | .Neg x => .Neg (norm x)
  | .Mul x y => .Mul (norm x) (norm y)
  | .Pow x n => powN (norm x) n

section Sem
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

theorem eval_powN (x : MixedExpr F) (eK : Env K) (eF : Env F) :
    ∀ n, (powN x n).eval eK eF = (x.eval eK eF) ^ n
  | 0 => by simp [powN, MixedExpr.eval]
  | n + 1 => by simp [powN, MixedExpr.eval, eval_powN x eK eF n, pow_succ]

/-- `norm` preserves the semantics of a mixed expression. -/
theorem eval_norm (eK : Env K) (eF : Env F) : ∀ e : MixedExpr F, (norm e).eval eK eF = e.eval eK eF
  | .Var k i => by cases k <;> rfl
  | .Lift g => rfl
  | .Scale g u => by simp [norm, MixedExpr.eval, eval_norm eK eF u]
  | .Const c => rfl
  | .Add x y => by simp [norm, MixedExpr.eval, eval_norm eK eF x, eval_norm eK eF y]
  | .Sub x y => by simp [norm, MixedExpr.eval, eval_norm eK eF x, eval_norm eK eF y]
  | .Neg x => by simp [norm, MixedExpr.eval, eval_norm eK eF x]
  | .Mul x y => by simp [norm, MixedExpr.eval, eval_norm eK eF x, eval_norm eK eF y]
  | .Pow x n => by simp [norm, MixedExpr.eval, eval_powN, eval_norm eK eF x]
end Sem

def emitPow (j : JExpr) : ℕ → JExpr
  | 0 => .extLift (.constZ 1)
  | n + 1 => .extMul (emitPow j n) j

def emitMixed : MixedExpr Gl → JExpr
  | .Var .traceCur i => .extVar i .traceCur
  | .Var .traceNext i => .extVar i .traceNext
  | .Var .challenge i => .extChal i
  | .Var .publicVal i => .extVar i .publicVal
  | .Lift g => .extLift (emitBase g)
  | .Scale g u => .extMul (.extLift (emitBase g)) (emitMixed u)
  | .Const c => .extLift (.constZ c)
  | .Add x y => .extAdd (emitMixed x) (emitMixed y)
  | .Sub x y => .extSub (emitMixed x) (emitMixed y)
  | .Neg x => .extNeg (emitMixed x)
  | .Mul x y => .extMul (emitMixed x) (emitMixed y)
  | .Pow x n => emitPow (emitMixed x) n

def decodeMixed : JExpr → Option (MixedExpr Gl)
  | .extVar i k => some (.Var k i)
  | .extChal i => some (.Var .challenge i)
  | .extLift (.constZ c) => some (.Const c)
  | .extLift g => (decodeBase g).map .Lift
  | .extAdd a b => match decodeMixed a, decodeMixed b with | some x, some y => some (.Add x y) | _, _ => none
  | .extSub a b => match decodeMixed a, decodeMixed b with | some x, some y => some (.Sub x y) | _, _ => none
  | .extMul a b => match decodeMixed a, decodeMixed b with | some x, some y => some (.Mul x y) | _, _ => none
  | .extNeg a => (decodeMixed a).map .Neg
  | _ => none

theorem decode_emitPow (j : JExpr) (d : MixedExpr Gl) (h : decodeMixed j = some d) :
    ∀ n, decodeMixed (emitPow j n) = some (powN d n)
  | 0 => by simp [emitPow, decodeMixed, powN]
  | n + 1 => by simp [emitPow, decodeMixed, powN, decode_emitPow j d h n, h]

theorem decode_extLift_emitBase (g : CoeffExpr Gl) :
    decodeMixed (.extLift (emitBase g)) = some (.Lift g) := by
  cases g <;> simp [emitBase, decodeMixed, decodeBase_emitBase, decodeBase]

theorem decodeMixed_emitMixed : ∀ e : MixedExpr Gl, decodeMixed (emitMixed e) = some (norm e)
  | .Var .traceCur i => rfl
  | .Var .traceNext i => rfl
  | .Var .challenge i => rfl
  | .Var .publicVal i => rfl
  | .Lift g => decode_extLift_emitBase g
  | .Scale g u => by
      simp [emitMixed, decodeMixed, norm]
      rw [decode_extLift_emitBase, decodeMixed_emitMixed u]
  | .Const c => rfl
  | .Add x y => by simp [emitMixed, decodeMixed, norm, decodeMixed_emitMixed x, decodeMixed_emitMixed y]
  | .Sub x y => by simp [emitMixed, decodeMixed, norm, decodeMixed_emitMixed x, decodeMixed_emitMixed y]
  | .Neg x => by simp [emitMixed, decodeMixed, norm, decodeMixed_emitMixed x]
  | .Mul x y => by simp [emitMixed, decodeMixed, norm, decodeMixed_emitMixed x, decodeMixed_emitMixed y]
  | .Pow x n => by
      simpa [emitMixed, norm] using decode_emitPow _ _ (decodeMixed_emitMixed x) n

/-! ## Gate lists of a chip template -/

/-- The emitted gate lists (the JSON `gate_lists`). -/
structure EGates where
  base : List JExpr
  ext : List JExpr
  mixed : List JExpr
  ext1 : List JExpr
  ext3 : List JExpr
  eqc : List JExpr
deriving Repr

def emitGates (T : ChipTemplate Gl) : EGates where
  base := T.baseTransition.map emitBase
  ext := T.extTransition.map fun e => emitMixed (MixedExpr.ofExpr e)
  mixed := T.mixedTransition.map emitMixed
  ext1 := T.extDeg1.map fun e => emitMixed (MixedExpr.ofExpr e)
  ext3 := T.extDeg3.map fun e => emitMixed (MixedExpr.ofExpr e)
  eqc := T.equalityChecks.map emitBase

/-- What the emitted gate lists decode to. -/
structure DGates where
  base : List (CoeffExpr Gl)
  ext : List (MixedExpr Gl)
  mixed : List (MixedExpr Gl)
  ext1 : List (MixedExpr Gl)
  ext3 : List (MixedExpr Gl)
  eqc : List (CoeffExpr Gl)

def decodeGates (g : EGates) : Option DGates :=
  match g.base.mapM decodeBase, g.ext.mapM decodeMixed, g.mixed.mapM decodeMixed,
        g.ext1.mapM decodeMixed, g.ext3.mapM decodeMixed, g.eqc.mapM decodeBase with
  | some a, some b, some c, some d, some e, some f => some ⟨a, b, c, d, e, f⟩
  | _, _, _, _, _, _ => none

theorem mapM_map_some {α β γ : Type} (f : β → Option γ) (g : α → β) (h : α → γ)
    (hh : ∀ x, f (g x) = some (h x)) : ∀ l : List α, (l.map g).mapM f = some (l.map h)
  | [] => rfl
  | x :: l => by simp [List.mapM_cons, hh x, mapM_map_some f g h hh l]

/-- The template's gate lists, in the normal form `norm` (the `𝕂′`-and-`Expr` buckets read as mixed). -/
def templateGates (T : ChipTemplate Gl) : DGates where
  base := T.baseTransition
  ext := T.extTransition.map fun e => norm (MixedExpr.ofExpr e)
  mixed := T.mixedTransition.map norm
  ext1 := T.extDeg1.map fun e => norm (MixedExpr.ofExpr e)
  ext3 := T.extDeg3.map fun e => norm (MixedExpr.ofExpr e)
  eqc := T.equalityChecks

/-- **Round trip of the emitter on any `ZMod p` chip template.** -/
theorem decode_emitGates (T : ChipTemplate Gl) : decodeGates (emitGates T) = some (templateGates T) := by
  have hb := mapM_map_some decodeBase emitBase id decodeBase_emitBase
  have hm := mapM_map_some decodeMixed emitMixed norm decodeMixed_emitMixed
  have hx := mapM_map_some decodeMixed (fun e : Expr => emitMixed (MixedExpr.ofExpr e))
    (fun e => norm (MixedExpr.ofExpr e)) (fun e => decodeMixed_emitMixed _)
  simp only [decodeGates, emitGates, templateGates, hb, hm, hx, List.map_id]

end Nock.Emit
