/-
  NockvmE2E/Emit/Tie.lean

  **The emitter tie, part A: `toEx` and the evaluation of a decoded DAG.**

  `toEx : JExpr → Option Tr.Ex` is the reading `Tr.parseEx` (Exec/Trace.lean:36-60) does of one JSON expression
  (`none` where `parseEx` throws: a `challenge` var kind).  `evalDagK_toEx_of_decodeDag` says: if the DAG document `d`
  decodes (with the list-table decoder `decodeDagL`) to the gate lists `g`, and `d`'s shared table and gate roots all
  parse, then the verifier's `KC` interpreter `evalDagK` of any chip whose `shared`/`cons` are those parses returns, in the
  JSON constraint order (base, ext, mixed, ext1, ext3, eqc), the `KC` values `evB`/`evM` of the decoded gates.

  `decodeDagL` is `decodeDag` with a `List` table in place of the `Lean.RBMap` one: neither core Lean nor Batteries (4.35) has
  `find?_insert` for `Lean.RBMap`.  The two are tied per emitted chip by `decide +kernel` (`Chips`/`TieChips`).
-/
import NockvmE2E.Emit.Dag
import NockvmE2E.Exec.DagSem

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Emit

open Nock.Emit Nock.Reified Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open NockvmE2E.Exec NockvmE2E.Exec.DagSem NockvmE2E.Exec.V NockvmE2E.Exec.VL

abbrev Ex := NockvmE2E.Exec.Tr.Ex

/-- `Tr.kindOf`, on the `VarKind`s the parser accepts. -/
def kindN : VarKind → Option ℕ
  | .traceCur => some 0
  | .traceNext => some 1
  | .publicVal => some 2
  | .challenge => none

def bin2 (op : Ex → Ex → Ex) (u v : Option Ex) : Option Ex :=
  match u, v with | some x, some y => some (op x y) | _, _ => none

/-- The reading `Tr.parseEx` does (`lift` / `ext_lift` are transparent; `ext_*` and base ops share constructors). -/
def toEx : JExpr → Option Ex
  | .ref i => some (.ref i)
  | .var k i => (kindN k).map fun n => .var n i
  | .extVar i k => (kindN k).map fun n => .extVar n i
  | .extChal i => some (.chal i)
  | .constF n => some (.cF (UInt64.ofNat (n % NockvmE2E.Exec.PF.P.toNat)))
  | .constZ z => some (.cF (NockvmE2E.Exec.Tr.ofInt z))
  | .add a b => bin2 .add (toEx a) (toEx b)
  | .sub a b => bin2 .sub (toEx a) (toEx b)
  | .mul a b => bin2 .mul (toEx a) (toEx b)
  | .neg a => (toEx a).map .neg
  | .pow a n => (toEx a).map (.pow · n)
  | .extLift a => toEx a
  | .extAdd a b => bin2 .add (toEx a) (toEx b)
  | .extSub a b => bin2 .sub (toEx a) (toEx b)
  | .extMul a b => bin2 .mul (toEx a) (toEx b)
  | .extNeg a => (toEx a).map .neg

theorem bin2_eq_some (op : Ex → Ex → Ex) (u v : Option Ex) (w : Ex) :
    bin2 op u v = some w ↔ ∃ x y, u = some x ∧ v = some y ∧ w = op x y := by
  rcases u with _ | x <;> rcases v with _ | y <;> simp [bin2, eq_comm]

/-! ## The `KC` semantics of decoded gates -/

/-- the residue of a `Gl` element in the verifier's `ZMod p` (`Nock.Field.p` and `Exec.p` are the same numeral) -/
def ofGl (c : Gl) : ZMod NockvmE2E.Exec.p := ((ZMod.val c : ℕ) : ZMod NockvmE2E.Exec.p)

/-- a public `𝕂`-value `e` = flat public slots `3e..3e+2` -/
noncomputable def pubK (env : KEnv) (e : ℕ) : KC :=
  algebraMap (ZMod NockvmE2E.Exec.p) KC (env.pub (3 * e)) + algebraMap (ZMod NockvmE2E.Exec.p) KC (env.pub (3 * e + 1)) * xr +
    algebraMap (ZMod NockvmE2E.Exec.p) KC (env.pub (3 * e + 2)) * xr ^ 2

/-- base-gate semantics in `KC` (`var` kinds as `evKC` reads them; `challenge` is never reached through `toEx`) -/
noncomputable def evB (env : KEnv) : CoeffExpr Gl → KC
  | .const c => algebraMap (ZMod NockvmE2E.Exec.p) KC (ofGl c)
  | .var .traceCur i => env.cur i
  | .var .traceNext i => env.next i
  | .var .challenge i => env.chal i
  | .var .publicVal i => algebraMap (ZMod NockvmE2E.Exec.p) KC (env.pub i)
  | .add a b => evB env a + evB env b
  | .sub a b => evB env a - evB env b
  | .mul a b => evB env a * evB env b
  | .neg a => - evB env a
  | .pow a n => evB env a ^ n

/-- mixed-gate semantics in `KC` (`𝕂`-columns read as `extK`) -/
noncomputable def evM (env : KEnv) : MixedExpr Gl → KC
  | .Var .traceCur i => extK env.cur env.bc i
  | .Var .traceNext i => extK env.next env.bc i
  | .Var .challenge i => env.chal i
  | .Var .publicVal i => pubK env i
  | .Lift g => evB env g
  | .Scale g u => evB env g * evM env u
  | .Const c => (c : KC)
  | .Add x y => evM env x + evM env y
  | .Sub x y => evM env x - evM env y
  | .Neg x => - evM env x
  | .Mul x y => evM env x * evM env y
  | .Pow x n => evM env x ^ n

noncomputable def valSem (env : KEnv) : Val → KC
  | .b c => evB env c
  | .m e => evM env e

/-! ## constants -/

theorem Pnat : NockvmE2E.Exec.PF.P.toNat = NockvmE2E.Exec.p := by decide +kernel

theorem zv_ofNat_mod (n : ℕ) : zv (UInt64.ofNat (n % NockvmE2E.Exec.PF.P.toNat)) = (n : ZMod NockvmE2E.Exec.p) := by
  have hp : n % NockvmE2E.Exec.PF.P.toNat < 2 ^ 64 :=
    lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  unfold zv
  rw [UInt64.toNat_ofNat_of_lt' hp, Pnat, ZMod.natCast_mod]

theorem zv_PFneg (a : UInt64) (ha : a.toNat < NockvmE2E.Exec.p) :
    zv (NockvmE2E.Exec.PF.neg a) = - zv a := by
  unfold NockvmE2E.Exec.PF.neg
  by_cases h : a = 0
  · subst h; simp [zv_zero]
  · have hb : (a == 0) = false := by simpa using h
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    have hle : a ≤ NockvmE2E.Exec.PF.P := by
      rw [UInt64.le_iff_toNat_le]; have : NockvmE2E.Exec.PF.P.toNat = NockvmE2E.Exec.p := Pnat
      omega
    unfold zv
    rw [UInt64.toNat_sub_of_le _ _ hle, Pnat, Nat.cast_sub (by omega), ZMod.natCast_self]; ring

theorem zv_ofInt (z : ℤ) : zv (NockvmE2E.Exec.Tr.ofInt z) = (z : ZMod NockvmE2E.Exec.p) := by
  unfold NockvmE2E.Exec.Tr.ofInt
  by_cases h : z ≥ 0
  · rw [if_pos h, zv_ofNat_mod]
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp
  · rw [if_neg h]
    have hlt : ((-z).toNat % NockvmE2E.Exec.PF.P.toNat) < NockvmE2E.Exec.p := by
      rw [Pnat]; exact Nat.mod_lt _ (by decide)
    have h1 : (UInt64.ofNat ((-z).toNat % NockvmE2E.Exec.PF.P.toNat)).toNat < NockvmE2E.Exec.p := by
      rw [UInt64.toNat_ofNat_of_lt' (lt_of_lt_of_le hlt (by decide))]; exact hlt
    rw [zv_PFneg _ h1, zv_ofNat_mod]
    have : (-z) = ((-z).toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
    have h2 : ((z : ℤ) : ZMod NockvmE2E.Exec.p) = - (((-z).toNat : ℕ) : ZMod NockvmE2E.Exec.p) := by
      have := congrArg (fun w : ℤ => (w : ZMod NockvmE2E.Exec.p)) this
      simp only [Int.cast_neg, Int.cast_natCast] at this
      linear_combination -this
    rw [h2]

/-! ## The list-table decoder -/

def dB2 (f : CoeffExpr Gl → CoeffExpr Gl → CoeffExpr Gl) (u v : Option Val) : Option Val :=
  match u, v with | some (.b x), some (.b y) => some (.b (f x y)) | _, _ => none
def dM2 (f : MixedExpr Gl → MixedExpr Gl → MixedExpr Gl) (u v : Option Val) : Option Val :=
  match u, v with | some (.m x), some (.m y) => some (.m (f x y)) | _, _ => none
def dB1 (f : CoeffExpr Gl → CoeffExpr Gl) (u : Option Val) : Option Val :=
  match u with | some (.b x) => some (.b (f x)) | _ => none
def dM1 (f : MixedExpr Gl → MixedExpr Gl) (u : Option Val) : Option Val :=
  match u with | some (.m x) => some (.m (f x)) | _ => none
def dLift (u : Option Val) : Option Val :=
  match u with | some (.b g) => some (.m (.Lift g)) | _ => none

theorem dB2_eq_some (f) (u v : Option Val) (w : Val) :
    dB2 f u v = some w ↔ ∃ x y, u = some (.b x) ∧ v = some (.b y) ∧ w = .b (f x y) := by
  rcases u with _ | (x | x) <;> rcases v with _ | (y | y) <;> simp [dB2, eq_comm]
theorem dM2_eq_some (f) (u v : Option Val) (w : Val) :
    dM2 f u v = some w ↔ ∃ x y, u = some (.m x) ∧ v = some (.m y) ∧ w = .m (f x y) := by
  rcases u with _ | (x | x) <;> rcases v with _ | (y | y) <;> simp [dM2, eq_comm]
theorem dB1_eq_some (f) (u : Option Val) (w : Val) :
    dB1 f u = some w ↔ ∃ x, u = some (.b x) ∧ w = .b (f x) := by
  rcases u with _ | (x | x) <;> simp [dB1, eq_comm]
theorem dM1_eq_some (f) (u : Option Val) (w : Val) :
    dM1 f u = some w ↔ ∃ x, u = some (.m x) ∧ w = .m (f x) := by
  rcases u with _ | (x | x) <;> simp [dM1, eq_comm]
theorem dLift_eq_some (u : Option Val) (w : Val) :
    dLift u = some w ↔ ∃ x, u = some (.b x) ∧ w = .m (.Lift x) := by
  rcases u with _ | (x | x) <;> simp [dLift, eq_comm]

/-- `decStep` with the table read through a lookup function (same cases as `Dag.lean`'s `decStep`) -/
def decStepG (lk : ℕ → Option Val) : JExpr → Option Val
  | .ref i => lk i
  | .var k i => some (.b (.var k i))
  | .constF n => some (.b (.const (n : Gl)))
  | .add a b => dB2 .add (decStepG lk a) (decStepG lk b)
  | .sub a b => dB2 .sub (decStepG lk a) (decStepG lk b)
  | .mul a b => dB2 .mul (decStepG lk a) (decStepG lk b)
  | .neg a => dB1 .neg (decStepG lk a)
  | .pow a n => dB1 (.pow · n) (decStepG lk a)
  | .extVar i k => some (.m (.Var k i))
  | .extChal i => some (.m (.Var .challenge i))
  | .extLift a => match a with
      | .constZ c => some (.m (.Const c))
      | _ => dLift (decStepG lk a)
  | .extAdd a b => dM2 .Add (decStepG lk a) (decStepG lk b)
  | .extSub a b => dM2 .Sub (decStepG lk a) (decStepG lk b)
  | .extMul a b => dM2 .Mul (decStepG lk a) (decStepG lk b)
  | .extNeg a => dM1 .Neg (decStepG lk a)
  | .constZ _ => none

/-- the table decoder over a `List` (entry `i` at index `i`) -/
def decTableL (defs : List JExpr) : Option (List Val) :=
  defs.foldlM (fun (l : List Val) j => (decStepG (fun i => l[i]?) j).map fun v => l ++ [v]) []

def decBL (l : List Val) (j : JExpr) : Option (CoeffExpr Gl) :=
  match decStepG (fun i => l[i]?) j with | some (.b g) => some g | _ => none
def decML (l : List Val) (j : JExpr) : Option (MixedExpr Gl) :=
  match decStepG (fun i => l[i]?) j with | some (.m g) => some g | _ => none

def decodeDagL (d : DagGates) : Option DGatesDec :=
  match decTableL d.defs with
  | none => none
  | some tab =>
    match d.base.mapM (decBL tab), d.ext.mapM (decML tab), d.mixed.mapM (decML tab),
          d.ext1.mapM (decML tab), d.ext3.mapM (decML tab), d.eqc.mapM (decBL tab) with
    | some a, some b, some c, some e, some f, some g => some ⟨a, b, c, e, f, g⟩
    | _, _, _, _, _, _ => none

/-! ## the memo invariant -/

/-- every decoded entry `i` of the table has been pushed, with its `KC` value, at memo index `i` -/
def Inv (env : KEnv) (l : List Val) (memo : Array KC) : Prop :=
  memo.size = l.length ∧ ∀ (i : ℕ) (v : Val), l[i]? = some v → memo[i]! = valSem env v

theorem Inv.empty (env : KEnv) : Inv env [] #[] := ⟨rfl, fun i v h => by simp at h⟩

theorem Inv.push {env : KEnv} {l : List Val} {memo : Array KC} (h : Inv env l memo) (v : Val) (x : KC)
    (hx : x = valSem env v) : Inv env (l ++ [v]) (memo.push x) := by
  obtain ⟨hs, hm⟩ := h
  refine ⟨by simp [hs], fun i w hw => ?_⟩
  by_cases hi : i < l.length
  · rw [List.getElem?_append_left hi] at hw
    have := hm i w hw
    rw [getElem!_pos memo i (by omega)] at this
    rw [getElem!_pos (memo.push x) i (by simp; omega), Array.getElem_push, dif_pos (by omega)]
    exact this
  · rw [List.getElem?_append_right (by omega)] at hw
    have hi2 : i = l.length := by
      by_contra hne
      have h3 : [v].length ≤ i - l.length := by simp; omega
      simp [List.getElem?_eq_none_iff.mpr h3] at hw
    subst hi2
    simp at hw
    subst hw
    rw [getElem!_pos (memo.push x) l.length (by simp [hs]), Array.getElem_push, dif_neg (by omega)]
    exact hx

theorem ofGl_natCast (n : ℕ) : ofGl (n : Gl) = (n : ZMod NockvmE2E.Exec.p) := by
  unfold ofGl
  have hq : Nock.Field.p = NockvmE2E.Exec.p := rfl
  rw [ZMod.val_natCast]
  rw [hq]
  exact ZMod.natCast_mod n _

/-- one decoded node, parsed, evaluates to its semantics (given a consistent memo) -/
theorem step_sem (env : KEnv) (l : List Val) (memo : Array KC) (hI : Inv env l memo) :
    ∀ (j : JExpr) (ex : Ex) (v : Val), toEx j = some ex → decStepG (fun i => l[i]?) j = some v →
      evKC env memo ex = valSem env v
  | .ref i, ex, v, h1, h2 => by
      simp only [toEx, Option.some.injEq] at h1; subst h1
      simp only [decStepG] at h2
      simp only [evKC]; exact hI.2 i v h2
  | .var k i, ex, v, h1, h2 => by
      simp only [decStepG, Option.some.injEq] at h2; subst h2
      cases k with
      | traceCur => simp only [toEx, kindN, Option.map_some, Option.some.injEq] at h1; subst h1; rfl
      | traceNext => simp only [toEx, kindN, Option.map_some, Option.some.injEq] at h1; subst h1; rfl
      | publicVal => simp only [toEx, kindN, Option.map_some, Option.some.injEq] at h1; subst h1; rfl
      | challenge => simp [toEx, kindN] at h1
  | .constF n, ex, v, h1, h2 => by
      simp only [decStepG, Option.some.injEq] at h2; subst h2
      simp only [toEx, Option.some.injEq] at h1; subst h1
      simp only [valSem, evKC, psiV, zv_ofNat_mod, evB, ofGl_natCast]
  | .constZ z, ex, v, h1, h2 => by simp [decStepG] at h2
  | .add a b, ex, v, h1, h2 => by
      simp only [toEx, bin2_eq_some] at h1
      obtain ⟨x, y, hx, hy, rfl⟩ := h1
      simp only [decStepG, dB2_eq_some] at h2
      obtain ⟨gx, gy, ha, hb, rfl⟩ := h2
      simp only [valSem, evKC, evB]
      rw [step_sem env l memo hI a x (.b gx) hx ha, step_sem env l memo hI b y (.b gy) hy hb]
      rfl
  | .sub a b, ex, v, h1, h2 => by
      simp only [toEx, bin2_eq_some] at h1
      obtain ⟨x, y, hx, hy, rfl⟩ := h1
      simp only [decStepG, dB2_eq_some] at h2
      obtain ⟨gx, gy, ha, hb, rfl⟩ := h2
      simp only [valSem, evKC, evB]
      rw [step_sem env l memo hI a x (.b gx) hx ha, step_sem env l memo hI b y (.b gy) hy hb]
      rfl
  | .mul a b, ex, v, h1, h2 => by
      simp only [toEx, bin2_eq_some] at h1
      obtain ⟨x, y, hx, hy, rfl⟩ := h1
      simp only [decStepG, dB2_eq_some] at h2
      obtain ⟨gx, gy, ha, hb, rfl⟩ := h2
      simp only [valSem, evKC, evB]
      rw [step_sem env l memo hI a x (.b gx) hx ha, step_sem env l memo hI b y (.b gy) hy hb]
      rfl
  | .neg a, ex, v, h1, h2 => by
      simp only [toEx, Option.map_eq_some_iff] at h1
      obtain ⟨x, hx, rfl⟩ := h1
      simp only [decStepG, dB1_eq_some] at h2
      obtain ⟨gx, ha, rfl⟩ := h2
      simp only [valSem, evKC, evB]
      rw [step_sem env l memo hI a x (.b gx) hx ha]
      rfl
  | .pow a n, ex, v, h1, h2 => by
      simp only [toEx, Option.map_eq_some_iff] at h1
      obtain ⟨x, hx, rfl⟩ := h1
      simp only [decStepG, dB1_eq_some] at h2
      obtain ⟨gx, ha, rfl⟩ := h2
      simp only [valSem, evKC, evB]
      rw [step_sem env l memo hI a x (.b gx) hx ha]
      rfl
  | .extVar i k, ex, v, h1, h2 => by
      simp only [decStepG, Option.some.injEq] at h2; subst h2
      cases k with
      | traceCur => simp only [toEx, kindN, Option.map_some, Option.some.injEq] at h1; subst h1; rfl
      | traceNext => simp only [toEx, kindN, Option.map_some, Option.some.injEq] at h1; subst h1; rfl
      | publicVal => simp only [toEx, kindN, Option.map_some, Option.some.injEq] at h1; subst h1; rfl
      | challenge => simp [toEx, kindN] at h1
  | .extChal i, ex, v, h1, h2 => by
      simp only [decStepG, Option.some.injEq] at h2; subst h2
      simp only [toEx, Option.some.injEq] at h1; subst h1; rfl
  | .extLift a, ex, v, h1, h2 => by
      by_cases hc : ∃ c, a = .constZ c
      · obtain ⟨c, rfl⟩ := hc
        simp only [decStepG, Option.some.injEq] at h2; subst h2
        simp only [toEx, Option.some.injEq] at h1; subst h1
        simp only [valSem, evKC, psiV, zv_ofInt, evM, map_intCast]
      · have hd : decStepG (fun i => l[i]?) (.extLift a) = dLift (decStepG (fun i => l[i]?) a) := by
          cases a <;> first | rfl | (exfalso; exact hc ⟨_, rfl⟩)
        rw [hd, dLift_eq_some] at h2
        obtain ⟨gx, ha, rfl⟩ := h2
        simp only [toEx] at h1
        have := step_sem env l memo hI a ex (.b gx) h1 ha
        exact this.trans rfl
  | .extAdd a b, ex, v, h1, h2 => by
      simp only [toEx, bin2_eq_some] at h1
      obtain ⟨x, y, hx, hy, rfl⟩ := h1
      simp only [decStepG, dM2_eq_some] at h2
      obtain ⟨gx, gy, ha, hb, rfl⟩ := h2
      simp only [valSem, evKC, evM]
      rw [step_sem env l memo hI a x (.m gx) hx ha, step_sem env l memo hI b y (.m gy) hy hb]
      rfl
  | .extSub a b, ex, v, h1, h2 => by
      simp only [toEx, bin2_eq_some] at h1
      obtain ⟨x, y, hx, hy, rfl⟩ := h1
      simp only [decStepG, dM2_eq_some] at h2
      obtain ⟨gx, gy, ha, hb, rfl⟩ := h2
      simp only [valSem, evKC, evM]
      rw [step_sem env l memo hI a x (.m gx) hx ha, step_sem env l memo hI b y (.m gy) hy hb]
      rfl
  | .extMul a b, ex, v, h1, h2 => by
      simp only [toEx, bin2_eq_some] at h1
      obtain ⟨x, y, hx, hy, rfl⟩ := h1
      simp only [decStepG, dM2_eq_some] at h2
      obtain ⟨gx, gy, ha, hb, rfl⟩ := h2
      simp only [valSem, evKC, evM]
      rw [step_sem env l memo hI a x (.m gx) hx ha, step_sem env l memo hI b y (.m gy) hy hb]
      rfl
  | .extNeg a, ex, v, h1, h2 => by
      simp only [toEx, Option.map_eq_some_iff] at h1
      obtain ⟨x, hx, rfl⟩ := h1
      simp only [decStepG, dM1_eq_some] at h2
      obtain ⟨gx, ha, rfl⟩ := h2
      simp only [valSem, evKC, evM]
      rw [step_sem env l memo hI a x (.m gx) hx ha]
      rfl

/-- the shared table: parse and decode agree, entry by entry -/
theorem tab_inv (env : KEnv) : ∀ (defs : List JExpr) (sh : List Ex) (l0 l : List Val) (memo : Array KC),
    Inv env l0 memo →
    defs.foldlM (fun (l : List Val) j => (decStepG (fun i => l[i]?) j).map fun v => l ++ [v]) l0 = some l →
    defs.mapM toEx = some sh →
    Inv env l (sh.foldl (fun memo s => memo.push (evKC env memo s)) memo)
  | [], sh, l0, l, memo, hI, h1, h2 => by
      simp at h1 h2; subst h1; subst h2; exact hI
  | j :: rest, sh, l0, l, memo, hI, h1, h2 => by
      rw [List.foldlM_cons] at h1
      cases hv : decStepG (fun i => l0[i]?) j with
      | none => simp [hv] at h1
      | some v =>
        simp only [hv, Option.map_some] at h1
        rw [List.mapM_cons] at h2
        cases hx : toEx j with
        | none => simp [hx] at h2
        | some ex =>
          cases hr : rest.mapM toEx with
          | none => simp [hx, hr] at h2
          | some sh' =>
            simp [hx, hr] at h2
            subst h2
            simp only [List.foldl_cons]
            exact tab_inv env rest sh' _ l _ (hI.push v _ (step_sem env l0 memo hI j ex v hx hv)) h1 hr

theorem mapM_sem {α : Type} (env : KEnv) (l : List Val) (memo : Array KC) (dec : JExpr → Option α) (sem : α → KC)
    (hdec : ∀ j ex a, toEx j = some ex → dec j = some a → evKC env memo ex = sem a) :
    ∀ (js : List JExpr) (exs : List Ex) (as : List α), js.mapM toEx = some exs → js.mapM dec = some as →
      exs.map (evKC env memo) = as.map sem
  | [], exs, as, h1, h2 => by simp at h1 h2; subst h1; subst h2; rfl
  | j :: rest, exs, as, h1, h2 => by
      rw [List.mapM_cons] at h1 h2
      cases hx : toEx j with
      | none => simp [hx] at h1
      | some ex =>
        cases hr : rest.mapM toEx with
        | none => simp [hx, hr] at h1
        | some exs' =>
          cases ha : dec j with
          | none => simp [ha] at h2
          | some a =>
            cases hs : rest.mapM dec with
            | none => simp [ha, hs] at h2
            | some as' =>
              simp [hx, hr] at h1
              simp [ha, hs] at h2
              subst h1; subst h2
              simp only [List.map_cons, hdec j ex a hx ha, mapM_sem env l memo dec sem hdec rest exs' as' hr hs]

/-- **`evalDagK_toEx_of_decodeDag`**. -/
theorem evalDagK_toEx_of_decodeDag (d : DagGates) (g : DGatesDec) (hd : decodeDagL d = some g)
    (sh : List Ex) (hsh : d.defs.mapM toEx = some sh)
    (cb ce cm c1 c3 cq : List Ex)
    (hcb : d.base.mapM toEx = some cb) (hce : d.ext.mapM toEx = some ce) (hcm : d.mixed.mapM toEx = some cm)
    (hc1 : d.ext1.mapM toEx = some c1) (hc3 : d.ext3.mapM toEx = some c3) (hcq : d.eqc.mapM toEx = some cq)
    (ch : NockvmE2E.Exec.Tr.Chip) (hsh' : ch.shared = sh.toArray)
    (hcons : ch.cons.toList.map (·.e) = cb ++ ce ++ cm ++ c1 ++ c3 ++ cq) (env : KEnv) :
    (evalDagK ch env).toList =
      g.base.map (evB env) ++ g.ext.map (evM env) ++ g.mixed.map (evM env) ++ g.ext1.map (evM env) ++
        g.ext3.map (evM env) ++ g.eqc.map (evB env) := by
  unfold decodeDagL at hd
  cases hl : decTableL d.defs with
  | none => simp [hl] at hd
  | some l =>
    simp only [hl] at hd
    have hI : Inv env l (memoK sh env) := by
      have := tab_inv env d.defs sh [] l #[] (Inv.empty env) hl hsh
      simpa [memoK, hsh'] using this
    cases ha : d.base.mapM (decBL l) with
    | none => simp [ha] at hd
    | some a =>
    cases hb : d.ext.mapM (decML l) with
    | none => simp [ha, hb] at hd
    | some b =>
    cases hc : d.mixed.mapM (decML l) with
    | none => simp [ha, hb, hc] at hd
    | some c =>
    cases he : d.ext1.mapM (decML l) with
    | none => simp [ha, hb, hc, he] at hd
    | some e =>
    cases hf : d.ext3.mapM (decML l) with
    | none => simp [ha, hb, hc, he, hf] at hd
    | some f =>
    cases hq : d.eqc.mapM (decBL l) with
    | none => simp [ha, hb, hc, he, hf, hq] at hd
    | some q =>
    simp only [ha, hb, hc, he, hf, hq, Option.some.injEq] at hd
    subst hd
    have hB : ∀ j ex a, toEx j = some ex → decBL l j = some a → evKC env (memoK sh env) ex = evB env a := by
      intro j ex a h1 h2
      unfold decBL at h2
      cases hs : decStepG (fun i => l[i]?) j with
      | none => simp [hs] at h2
      | some w =>
        cases w with
        | b g => simp only [hs, Option.some.injEq] at h2; subst h2; exact step_sem env l _ hI j ex _ h1 hs
        | m g => simp [hs] at h2
    have hM : ∀ j ex a, toEx j = some ex → decML l j = some a → evKC env (memoK sh env) ex = evM env a := by
      intro j ex a h1 h2
      unfold decML at h2
      cases hs : decStepG (fun i => l[i]?) j with
      | none => simp [hs] at h2
      | some w =>
        cases w with
        | b g => simp [hs] at h2
        | m g => simp only [hs, Option.some.injEq] at h2; subst h2; exact step_sem env l _ hI j ex _ h1 hs
    unfold evalDagK
    rw [← Array.toList_map, Array.toList_map]
    simp only [Array.toList_map]
    have hmemo : memoK ch.shared.toList env = memoK sh env := by simp [hsh']
    rw [hmemo]
    have : ch.cons.toList.map (fun c => evKC env (memoK sh env) c.e) =
        (ch.cons.toList.map (·.e)).map (evKC env (memoK sh env)) := by simp [List.map_map, Function.comp_def]
    rw [this, hcons]
    simp only [List.map_append]
    rw [mapM_sem env l _ _ _ hB _ _ _ hcb ha, mapM_sem env l _ _ _ hM _ _ _ hce hb,
      mapM_sem env l _ _ _ hM _ _ _ hcm hc, mapM_sem env l _ _ _ hM _ _ _ hc1 he,
      mapM_sem env l _ _ _ hM _ _ _ hc3 hf, mapM_sem env l _ _ _ hB _ _ _ hcq hq]

end NockvmE2E.Emit

#print axioms NockvmE2E.Emit.evalDagK_toEx_of_decodeDag
#print axioms NockvmE2E.Emit.step_sem
#print axioms NockvmE2E.Emit.zv_ofInt
