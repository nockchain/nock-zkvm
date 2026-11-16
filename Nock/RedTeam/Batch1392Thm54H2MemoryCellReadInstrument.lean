/-
  Nock/RedTeam/Batch1392Thm54H2MemoryCellReadInstrument.lean

  The deployed memory chip's `𝕂` gates are `MixedExpr`s (`mixedTransitionGates`): `𝕂`-leaves
  `Var kind r` read the gathered `𝕂` role `r`; base leaves sit inside `Lift` / `Scale` as
  `CoeffExpr`s.  On an accepted row the four state selectors (base columns `0..3`), the masks
  (`4`, `5`) and the root mask (`153`) are known `0/1` values.  `MS` is the gate's SHAPE with every
  base-field constant kept opaque (`CS.opq x`, never inspected) and the known base columns
  replaced by integers; `simpMS` folds the integers.  Both steps are sound for `MixedExpr.eval`
  (`toMS_eval`, `simpMS_eval`), so a role the folded shape does not read is a role the gate does
  not read ON THAT CELL (`evalMS_congr`).  Every receipt is `rfl` at the generic carrier (the
  kernel never inspects an opaque constant): the pattern of `DeployedStaging.memory_mixed_reads`.
-/
import Nock.NockVMROM.Thm54.DeployedStaging

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1392

open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler

/-! ## A. Shapes -/

/-- A base-field expression with known integer cells and opaque constants. -/
inductive CS (F : Type*) where
  | kn : ℤ → CS F
  | col : VarKind → ℕ → CS F
  | opq : F → CS F
  | add : CS F → CS F → CS F
  | sub : CS F → CS F → CS F
  | mul : CS F → CS F → CS F
  | neg : CS F → CS F
  | pow : CS F → ℕ → CS F

/-- A mixed expression over `CS`. -/
inductive MS (F : Type*) where
  | var : VarKind → ℕ → MS F
  | lift : CS F → MS F
  | scale : CS F → MS F → MS F
  | cnst : ℤ → MS F
  | add : MS F → MS F → MS F
  | sub : MS F → MS F → MS F
  | neg : MS F → MS F
  | mul : MS F → MS F → MS F
  | pow : MS F → ℕ → MS F

variable {F : Type*}

/-- Translate, replacing the known base cells (`known kind col`). -/
def toCS (known : VarKind → ℕ → Option ℤ) : CoeffExpr F → CS F
  | .const x => .opq x
  | .var k c => match known k c with | some v => .kn v | none => .col k c
  | .add a b => .add (toCS known a) (toCS known b)
  | .sub a b => .sub (toCS known a) (toCS known b)
  | .mul a b => .mul (toCS known a) (toCS known b)
  | .neg a => .neg (toCS known a)
  | .pow a n => .pow (toCS known a) n

def toMS (known : VarKind → ℕ → Option ℤ) : MixedExpr F → MS F
  | .Var k i => .var k i
  | .Lift g => .lift (toCS known g)
  | .Scale g u => .scale (toCS known g) (toMS known u)
  | .Const c => .cnst c
  | .Add x y => .add (toMS known x) (toMS known y)
  | .Sub x y => .sub (toMS known x) (toMS known y)
  | .Neg x => .neg (toMS known x)
  | .Mul x y => .mul (toMS known x) (toMS known y)
  | .Pow x n => .pow (toMS known x) n

def CS.isKn : CS F → Option ℤ
  | .kn v => some v
  | _ => none

def MS.isCn : MS F → Option ℤ
  | .cnst v => some v
  | _ => none

def mkAddC (x y : CS F) : CS F :=
  match x.isKn, y.isKn with
  | some a, some b => .kn (a + b)
  | some a, none => if a = 0 then y else .add x y
  | none, some b => if b = 0 then x else .add x y
  | none, none => .add x y
def mkSubC (x y : CS F) : CS F :=
  match x.isKn, y.isKn with
  | some a, some b => .kn (a - b)
  | none, some b => if b = 0 then x else .sub x y
  | _, _ => .sub x y
def mkMulC (x y : CS F) : CS F :=
  match x.isKn, y.isKn with
  | some a, some b => .kn (a * b)
  | some a, none => if a = 0 then .kn 0 else if a = 1 then y else .mul x y
  | none, some b => if b = 0 then .kn 0 else if b = 1 then x else .mul x y
  | none, none => .mul x y
def mkNegC (x : CS F) : CS F :=
  match x.isKn with | some a => .kn (-a) | none => .neg x
def mkPowC (x : CS F) (n : ℕ) : CS F :=
  match x.isKn with | some a => .kn (a ^ n) | none => .pow x n

def simpCS : CS F → CS F
  | .add a b => mkAddC (simpCS a) (simpCS b)
  | .sub a b => mkSubC (simpCS a) (simpCS b)
  | .mul a b => mkMulC (simpCS a) (simpCS b)
  | .neg a => mkNegC (simpCS a)
  | .pow a n => mkPowC (simpCS a) n
  | t => t

def mkLift (g : CS F) : MS F :=
  match g.isKn with | some v => .cnst v | none => .lift g
def mkScale (g : CS F) (u : MS F) : MS F :=
  match g.isKn with
  | some v => if v = 0 then .cnst 0 else if v = 1 then u else .scale g u
  | none => .scale g u
def mkAddM (x y : MS F) : MS F :=
  match x.isCn, y.isCn with
  | some a, some b => .cnst (a + b)
  | some a, none => if a = 0 then y else .add x y
  | none, some b => if b = 0 then x else .add x y
  | none, none => .add x y
def mkSubM (x y : MS F) : MS F :=
  match x.isCn, y.isCn with
  | some a, some b => .cnst (a - b)
  | none, some b => if b = 0 then x else .sub x y
  | _, _ => .sub x y
def mkMulM (x y : MS F) : MS F :=
  match x.isCn, y.isCn with
  | some a, some b => .cnst (a * b)
  | some a, none => if a = 0 then .cnst 0 else if a = 1 then y else .mul x y
  | none, some b => if b = 0 then .cnst 0 else if b = 1 then x else .mul x y
  | none, none => .mul x y
def mkNegM (x : MS F) : MS F :=
  match x.isCn with | some a => .cnst (-a) | none => .neg x
def mkPowM (x : MS F) (n : ℕ) : MS F :=
  match x.isCn with | some a => .cnst (a ^ n) | none => .pow x n

def simpMS : MS F → MS F
  | .lift g => mkLift (simpCS g)
  | .scale g u => mkScale (simpCS g) (simpMS u)
  | .add x y => mkAddM (simpMS x) (simpMS y)
  | .sub x y => mkSubM (simpMS x) (simpMS y)
  | .mul x y => mkMulM (simpMS x) (simpMS y)
  | .neg x => mkNegM (simpMS x)
  | .pow x n => mkPowM (simpMS x) n
  | t => t

/-- The cell specialization. -/
def specM (known : VarKind → ℕ → Option ℤ) (g : MixedExpr F) : MS F := simpMS (toMS known g)

/-! ## B. Semantics and soundness -/

section Eval

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

def evalCS (eF : Env F) : CS F → F
  | .kn v => (v : F)
  | .col .traceCur c => eF.trace c
  | .col .traceNext c => eF.traceNext c
  | .col .challenge c => eF.chal c
  | .col .publicVal c => eF.pub c
  | .opq x => x
  | .add a b => evalCS eF a + evalCS eF b
  | .sub a b => evalCS eF a - evalCS eF b
  | .mul a b => evalCS eF a * evalCS eF b
  | .neg a => -evalCS eF a
  | .pow a n => evalCS eF a ^ n

def evalMS (eK : Env K) (eF : Env F) : MS F → K
  | .var .traceCur i => eK.trace i
  | .var .traceNext i => eK.traceNext i
  | .var .challenge i => eK.chal i
  | .var .publicVal i => eK.pub i
  | .lift g => algebraMap F K (evalCS eF g)
  | .scale g u => algebraMap F K (evalCS eF g) * evalMS eK eF u
  | .cnst c => (c : K)
  | .add x y => evalMS eK eF x + evalMS eK eF y
  | .sub x y => evalMS eK eF x - evalMS eK eF y
  | .neg x => -evalMS eK eF x
  | .mul x y => evalMS eK eF x * evalMS eK eF y
  | .pow x n => evalMS eK eF x ^ n

def envAtF (e : Env F) : VarKind → ℕ → F
  | .traceCur, i => e.trace i
  | .traceNext, i => e.traceNext i
  | .challenge, i => e.chal i
  | .publicVal, i => e.pub i

/-- An `F`-environment carries the known base cells. -/
def Carries (eF : Env F) (known : VarKind → ℕ → Option ℤ) : Prop :=
  ∀ k c v, known k c = some v → envAtF eF k c = (v : F)

theorem toCS_eval (eF : Env F) (known : VarKind → ℕ → Option ℤ) (h : Carries eF known) :
    ∀ g : CoeffExpr F, evalCS eF (toCS known g) = g.eval eF
  | .const _ => rfl
  | .var k c => by
      simp only [toCS]
      rcases hc : known k c with _ | v
      · cases k <;> rfl
      · have := h k c v hc
        cases k <;> simp only [evalCS, CoeffExpr.eval] <;> exact this.symm
  | .add a b => by
      simp only [toCS, evalCS, CoeffExpr.eval, toCS_eval eF known h a, toCS_eval eF known h b]
  | .sub a b => by
      simp only [toCS, evalCS, CoeffExpr.eval, toCS_eval eF known h a, toCS_eval eF known h b]
  | .mul a b => by
      simp only [toCS, evalCS, CoeffExpr.eval, toCS_eval eF known h a, toCS_eval eF known h b]
  | .neg a => by simp only [toCS, evalCS, CoeffExpr.eval, toCS_eval eF known h a]
  | .pow a n => by simp only [toCS, evalCS, CoeffExpr.eval, toCS_eval eF known h a]

theorem toMS_eval (eK : Env K) (eF : Env F) (known : VarKind → ℕ → Option ℤ) (h : Carries eF known) :
    ∀ g : MixedExpr F, evalMS eK eF (toMS known g) = g.eval eK eF
  | .Var .traceCur _ => rfl
  | .Var .traceNext _ => rfl
  | .Var .challenge _ => rfl
  | .Var .publicVal _ => rfl
  | .Lift g => by simp only [toMS, evalMS, MixedExpr.eval, toCS_eval eF known h g]
  | .Scale g u => by
      simp only [toMS, evalMS, MixedExpr.eval, toCS_eval eF known h g, toMS_eval eK eF known h u]
  | .Const _ => rfl
  | .Add x y => by
      simp only [toMS, evalMS, MixedExpr.eval, toMS_eval eK eF known h x,
        toMS_eval eK eF known h y]
  | .Sub x y => by
      simp only [toMS, evalMS, MixedExpr.eval, toMS_eval eK eF known h x,
        toMS_eval eK eF known h y]
  | .Neg x => by simp only [toMS, evalMS, MixedExpr.eval, toMS_eval eK eF known h x]
  | .Mul x y => by
      simp only [toMS, evalMS, MixedExpr.eval, toMS_eval eK eF known h x,
        toMS_eval eK eF known h y]
  | .Pow x n => by simp only [toMS, evalMS, MixedExpr.eval, toMS_eval eK eF known h x]

theorem isKn_some {x : CS F} {a : ℤ} (h : x.isKn = some a) : x = .kn a := by
  cases x <;> simp_all [CS.isKn]

theorem isCn_some {x : MS F} {a : ℤ} (h : x.isCn = some a) : x = .cnst a := by
  cases x <;> simp_all [MS.isCn]

theorem mkAddC_eval (eF : Env F) (x y : CS F) :
    evalCS eF (mkAddC x y) = evalCS eF x + evalCS eF y := by
  unfold mkAddC
  rcases hx : x.isKn with _ | a <;> rcases hy : y.isKn with _ | b
  · rfl
  · simp only; split_ifs with hb
    · rw [isKn_some hy, hb]; simp [evalCS]
    · rfl
  · simp only; split_ifs with ha
    · rw [isKn_some hx, ha]; simp [evalCS]
    · rfl
  · rw [isKn_some hx, isKn_some hy]; simp [evalCS]

theorem mkSubC_eval (eF : Env F) (x y : CS F) :
    evalCS eF (mkSubC x y) = evalCS eF x - evalCS eF y := by
  unfold mkSubC
  rcases hx : x.isKn with _ | a <;> rcases hy : y.isKn with _ | b
  · rfl
  · simp only; split_ifs with hb
    · rw [isKn_some hy, hb]; simp [evalCS]
    · rfl
  · rfl
  · rw [isKn_some hx, isKn_some hy]; simp [evalCS]

theorem mkMulC_eval (eF : Env F) (x y : CS F) :
    evalCS eF (mkMulC x y) = evalCS eF x * evalCS eF y := by
  unfold mkMulC
  rcases hx : x.isKn with _ | a <;> rcases hy : y.isKn with _ | b
  · rfl
  · simp only; split_ifs with hb hb1
    · rw [isKn_some hy, hb]; simp [evalCS]
    · rw [isKn_some hy, hb1]; simp [evalCS]
    · rfl
  · simp only; split_ifs with ha ha1
    · rw [isKn_some hx, ha]; simp [evalCS]
    · rw [isKn_some hx, ha1]; simp [evalCS]
    · rfl
  · rw [isKn_some hx, isKn_some hy]; simp [evalCS]

theorem mkNegC_eval (eF : Env F) (x : CS F) : evalCS eF (mkNegC x) = -evalCS eF x := by
  unfold mkNegC
  rcases hx : x.isKn with _ | a
  · rfl
  · rw [isKn_some hx]; simp [evalCS]

theorem mkPowC_eval (eF : Env F) (x : CS F) (n : ℕ) :
    evalCS eF (mkPowC x n) = evalCS eF x ^ n := by
  unfold mkPowC
  rcases hx : x.isKn with _ | a
  · rfl
  · rw [isKn_some hx]; simp [evalCS]

theorem simpCS_eval (eF : Env F) : ∀ g : CS F, evalCS eF (simpCS g) = evalCS eF g
  | .add a b => by rw [simpCS, mkAddC_eval, simpCS_eval eF a, simpCS_eval eF b]; rfl
  | .sub a b => by rw [simpCS, mkSubC_eval, simpCS_eval eF a, simpCS_eval eF b]; rfl
  | .mul a b => by rw [simpCS, mkMulC_eval, simpCS_eval eF a, simpCS_eval eF b]; rfl
  | .neg a => by rw [simpCS, mkNegC_eval, simpCS_eval eF a]; rfl
  | .pow a n => by rw [simpCS, mkPowC_eval, simpCS_eval eF a]; rfl
  | .kn _ => rfl | .col _ _ => rfl | .opq _ => rfl

theorem mkLift_eval (eK : Env K) (eF : Env F) (g : CS F) :
    evalMS eK eF (mkLift g) = algebraMap F K (evalCS eF g) := by
  unfold mkLift
  rcases hg : g.isKn with _ | v
  · rfl
  · rw [isKn_some hg]; simp [evalMS, evalCS]

theorem mkScale_eval (eK : Env K) (eF : Env F) (g : CS F) (u : MS F) :
    evalMS eK eF (mkScale g u) = algebraMap F K (evalCS eF g) * evalMS eK eF u := by
  unfold mkScale
  rcases hg : g.isKn with _ | v
  · rfl
  · simp only
    split_ifs with h0 h1
    · rw [isKn_some hg, h0]; simp [evalMS, evalCS]
    · rw [isKn_some hg, h1]; simp [evalCS]
    · rfl

theorem mkAddM_eval (eK : Env K) (eF : Env F) (x y : MS F) :
    evalMS eK eF (mkAddM x y) = evalMS eK eF x + evalMS eK eF y := by
  unfold mkAddM
  rcases hx : x.isCn with _ | a <;> rcases hy : y.isCn with _ | b
  · rfl
  · simp only; split_ifs with hb
    · rw [isCn_some hy, hb]; simp [evalMS]
    · rfl
  · simp only; split_ifs with ha
    · rw [isCn_some hx, ha]; simp [evalMS]
    · rfl
  · rw [isCn_some hx, isCn_some hy]; simp [evalMS]

theorem mkSubM_eval (eK : Env K) (eF : Env F) (x y : MS F) :
    evalMS eK eF (mkSubM x y) = evalMS eK eF x - evalMS eK eF y := by
  unfold mkSubM
  rcases hx : x.isCn with _ | a <;> rcases hy : y.isCn with _ | b
  · rfl
  · simp only; split_ifs with hb
    · rw [isCn_some hy, hb]; simp [evalMS]
    · rfl
  · rfl
  · rw [isCn_some hx, isCn_some hy]; simp [evalMS]

theorem mkMulM_eval (eK : Env K) (eF : Env F) (x y : MS F) :
    evalMS eK eF (mkMulM x y) = evalMS eK eF x * evalMS eK eF y := by
  unfold mkMulM
  rcases hx : x.isCn with _ | a <;> rcases hy : y.isCn with _ | b
  · rfl
  · simp only; split_ifs with hb hb1
    · rw [isCn_some hy, hb]; simp [evalMS]
    · rw [isCn_some hy, hb1]; simp [evalMS]
    · rfl
  · simp only; split_ifs with ha ha1
    · rw [isCn_some hx, ha]; simp [evalMS]
    · rw [isCn_some hx, ha1]; simp [evalMS]
    · rfl
  · rw [isCn_some hx, isCn_some hy]; simp [evalMS]

theorem mkNegM_eval (eK : Env K) (eF : Env F) (x : MS F) :
    evalMS eK eF (mkNegM x) = -evalMS eK eF x := by
  unfold mkNegM
  rcases hx : x.isCn with _ | a
  · rfl
  · rw [isCn_some hx]; simp [evalMS]

theorem mkPowM_eval (eK : Env K) (eF : Env F) (x : MS F) (n : ℕ) :
    evalMS eK eF (mkPowM x n) = evalMS eK eF x ^ n := by
  unfold mkPowM
  rcases hx : x.isCn with _ | a
  · rfl
  · rw [isCn_some hx]; simp [evalMS]

theorem simpMS_eval (eK : Env K) (eF : Env F) : ∀ g : MS F, evalMS eK eF (simpMS g) = evalMS eK eF g
  | .lift g => by rw [simpMS, mkLift_eval, simpCS_eval]; rfl
  | .scale g u => by rw [simpMS, mkScale_eval, simpCS_eval, simpMS_eval eK eF u]; rfl
  | .add x y => by rw [simpMS, mkAddM_eval, simpMS_eval eK eF x, simpMS_eval eK eF y]; rfl
  | .sub x y => by rw [simpMS, mkSubM_eval, simpMS_eval eK eF x, simpMS_eval eK eF y]; rfl
  | .mul x y => by rw [simpMS, mkMulM_eval, simpMS_eval eK eF x, simpMS_eval eK eF y]; rfl
  | .neg x => by rw [simpMS, mkNegM_eval, simpMS_eval eK eF x]; rfl
  | .pow x n => by rw [simpMS, mkPowM_eval, simpMS_eval eK eF x]; rfl
  | .var _ _ => rfl | .cnst _ => rfl

theorem specM_eval (eK : Env K) (eF : Env F) (known : VarKind → ℕ → Option ℤ) (h : Carries eF known)
    (g : MixedExpr F) : evalMS eK eF (specM known g) = g.eval eK eF := by
  rw [specM, simpMS_eval, toMS_eval eK eF known h]

end Eval

/-! ## C. Read sets and the congruence they license -/

def readsCS : CS F → List (VarKind × ℕ)
  | .col k c => [(k, c)]
  | .add a b | .sub a b | .mul a b => readsCS a ++ readsCS b
  | .neg a | .pow a _ => readsCS a
  | _ => []

/-- `𝕂`-role reads `(kind, role)` and base-column reads `(kind, col)` of a shape. -/
def kReads : MS F → List (VarKind × ℕ)
  | .var k i => [(k, i)]
  | .scale _ u => kReads u
  | .add x y | .sub x y | .mul x y => kReads x ++ kReads y
  | .neg x | .pow x _ => kReads x
  | _ => []

def bReads : MS F → List (VarKind × ℕ)
  | .lift g => readsCS g
  | .scale g u => readsCS g ++ bReads u
  | .add x y | .sub x y | .mul x y => bReads x ++ bReads y
  | .neg x | .pow x _ => bReads x
  | _ => []

section Congr

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

def envAtK (e : Env K) : VarKind → ℕ → K
  | .traceCur, i => e.trace i
  | .traceNext, i => e.traceNext i
  | .challenge, i => e.chal i
  | .publicVal, i => e.pub i

theorem evalCS_congr (eF eF' : Env F) :
    ∀ g : CS F, (∀ v ∈ readsCS g, envAtK eF v.1 v.2 = envAtK eF' v.1 v.2) →
      evalCS eF g = evalCS eF' g
  | .kn _, _ => rfl
  | .opq _, _ => rfl
  | .col .traceCur c, h => h (.traceCur, c) (by simp [readsCS])
  | .col .traceNext c, h => h (.traceNext, c) (by simp [readsCS])
  | .col .challenge c, h => h (.challenge, c) (by simp [readsCS])
  | .col .publicVal c, h => h (.publicVal, c) (by simp [readsCS])
  | .add a b, h => by
      simp only [evalCS]
      rw [evalCS_congr eF eF' a (fun v hv => h v (by simp [readsCS, hv])),
        evalCS_congr eF eF' b (fun v hv => h v (by simp [readsCS, hv]))]
  | .sub a b, h => by
      simp only [evalCS]
      rw [evalCS_congr eF eF' a (fun v hv => h v (by simp [readsCS, hv])),
        evalCS_congr eF eF' b (fun v hv => h v (by simp [readsCS, hv]))]
  | .mul a b, h => by
      simp only [evalCS]
      rw [evalCS_congr eF eF' a (fun v hv => h v (by simp [readsCS, hv])),
        evalCS_congr eF eF' b (fun v hv => h v (by simp [readsCS, hv]))]
  | .neg a, h => by
      simp only [evalCS]; rw [evalCS_congr eF eF' a (fun v hv => h v (by simp [readsCS, hv]))]
  | .pow a _, h => by
      simp only [evalCS]; rw [evalCS_congr eF eF' a (fun v hv => h v (by simp [readsCS, hv]))]

theorem evalMS_congr (eK eK' : Env K) (eF eF' : Env F) :
    ∀ g : MS F, (∀ v ∈ kReads g, envAtK eK v.1 v.2 = envAtK eK' v.1 v.2) →
      (∀ v ∈ bReads g, envAtK eF v.1 v.2 = envAtK eF' v.1 v.2) →
      evalMS eK eF g = evalMS eK' eF' g
  | .var .traceCur i, hk, _ => hk (.traceCur, i) (by simp [kReads])
  | .var .traceNext i, hk, _ => hk (.traceNext, i) (by simp [kReads])
  | .var .challenge i, hk, _ => hk (.challenge, i) (by simp [kReads])
  | .var .publicVal i, hk, _ => hk (.publicVal, i) (by simp [kReads])
  | .lift g, _, hb => by
      simp only [evalMS]; rw [evalCS_congr eF eF' g (fun v hv => hb v (by simpa [bReads] using hv))]
  | .scale g u, hk, hb => by
      simp only [evalMS]
      rw [evalCS_congr eF eF' g (fun v hv => hb v (by simp [bReads, hv])),
        evalMS_congr eK eK' eF eF' u (fun v hv => hk v (by simpa [kReads] using hv))
          (fun v hv => hb v (by simp [bReads, hv]))]
  | .cnst _, _, _ => rfl
  | .add x y, hk, hb => by
      simp only [evalMS]
      rw [evalMS_congr eK eK' eF eF' x (fun v hv => hk v (by simp [kReads, hv]))
          (fun v hv => hb v (by simp [bReads, hv])),
        evalMS_congr eK eK' eF eF' y (fun v hv => hk v (by simp [kReads, hv]))
          (fun v hv => hb v (by simp [bReads, hv]))]
  | .sub x y, hk, hb => by
      simp only [evalMS]
      rw [evalMS_congr eK eK' eF eF' x (fun v hv => hk v (by simp [kReads, hv]))
          (fun v hv => hb v (by simp [bReads, hv])),
        evalMS_congr eK eK' eF eF' y (fun v hv => hk v (by simp [kReads, hv]))
          (fun v hv => hb v (by simp [bReads, hv]))]
  | .mul x y, hk, hb => by
      simp only [evalMS]
      rw [evalMS_congr eK eK' eF eF' x (fun v hv => hk v (by simp [kReads, hv]))
          (fun v hv => hb v (by simp [bReads, hv])),
        evalMS_congr eK eK' eF eF' y (fun v hv => hk v (by simp [kReads, hv]))
          (fun v hv => hb v (by simp [bReads, hv]))]
  | .neg x, hk, hb => by
      simp only [evalMS]
      rw [evalMS_congr eK eK' eF eF' x (fun v hv => hk v (by simp [kReads, hv]))
          (fun v hv => hb v (by simp [bReads, hv]))]
  | .pow x _, hk, hb => by
      simp only [evalMS]
      rw [evalMS_congr eK eK' eF eF' x (fun v hv => hk v (by simp [kReads, hv]))
          (fun v hv => hb v (by simp [bReads, hv]))]

end Congr


/-! ## C'. Raw read sets bound the specialized ones -/

/-- Raw `𝕂` reads of a gate (no specialization). -/
def rawK : MixedExpr F → List (VarKind × ℕ)
  | .Var k i => [(k, i)]
  | .Scale _ u => rawK u
  | .Add x y | .Sub x y | .Mul x y => rawK x ++ rawK y
  | .Neg x | .Pow x _ => rawK x
  | _ => []

def rawCS : CoeffExpr F → List (VarKind × ℕ)
  | .var k c => [(k, c)]
  | .add a b | .sub a b | .mul a b => rawCS a ++ rawCS b
  | .neg a | .pow a _ => rawCS a
  | _ => []

/-- Raw base reads of a gate. -/
def rawB : MixedExpr F → List (VarKind × ℕ)
  | .Lift g => rawCS g
  | .Scale g u => rawCS g ++ rawB u
  | .Add x y | .Sub x y | .Mul x y => rawB x ++ rawB y
  | .Neg x | .Pow x _ => rawB x
  | _ => []

theorem readsCS_toCS (known : VarKind → ℕ → Option ℤ) :
    ∀ (g : CoeffExpr F), ∀ v ∈ readsCS (toCS known g), v ∈ rawCS g
  | .const _, v, hv => by simp [toCS, readsCS] at hv
  | .var k c, v, hv => by
      simp only [toCS] at hv
      rcases hc : known k c with _ | w <;> simp_all [readsCS, rawCS]
  | .add a b, v, hv => by
      simp only [toCS, readsCS, List.mem_append] at hv
      simp only [rawCS, List.mem_append]
      rcases hv with h | h
      · exact Or.inl (readsCS_toCS known a v h)
      · exact Or.inr (readsCS_toCS known b v h)
  | .sub a b, v, hv => by
      simp only [toCS, readsCS, List.mem_append] at hv
      simp only [rawCS, List.mem_append]
      rcases hv with h | h
      · exact Or.inl (readsCS_toCS known a v h)
      · exact Or.inr (readsCS_toCS known b v h)
  | .mul a b, v, hv => by
      simp only [toCS, readsCS, List.mem_append] at hv
      simp only [rawCS, List.mem_append]
      rcases hv with h | h
      · exact Or.inl (readsCS_toCS known a v h)
      · exact Or.inr (readsCS_toCS known b v h)
  | .neg a, v, hv => by
      simp only [toCS, readsCS] at hv; simp only [rawCS]; exact readsCS_toCS known a v hv
  | .pow a _, v, hv => by
      simp only [toCS, readsCS] at hv; simp only [rawCS]; exact readsCS_toCS known a v hv

theorem readsCS_mkAddC (x y : CS F) : ∀ v ∈ readsCS (mkAddC x y), v ∈ readsCS x ++ readsCS y := by
  intro v hv; unfold mkAddC at hv
  rcases hx : x.isKn with _ | a <;> rcases hy : y.isKn with _ | b <;> simp only [hx, hy] at hv
  · simpa [readsCS] using hv
  · split_ifs at hv <;> simp_all [readsCS]
  · split_ifs at hv <;> simp_all [readsCS]
  · simp [readsCS] at hv
theorem readsCS_mkSubC (x y : CS F) : ∀ v ∈ readsCS (mkSubC x y), v ∈ readsCS x ++ readsCS y := by
  intro v hv; unfold mkSubC at hv
  rcases hx : x.isKn with _ | a <;> rcases hy : y.isKn with _ | b <;> simp only [hx, hy] at hv
  · simpa [readsCS] using hv
  · split_ifs at hv <;> simp_all [readsCS]
  · simpa [readsCS] using hv
  · simp [readsCS] at hv
theorem readsCS_mkMulC (x y : CS F) : ∀ v ∈ readsCS (mkMulC x y), v ∈ readsCS x ++ readsCS y := by
  intro v hv; unfold mkMulC at hv
  rcases hx : x.isKn with _ | a <;> rcases hy : y.isKn with _ | b <;> simp only [hx, hy] at hv
  · simpa [readsCS] using hv
  · split_ifs at hv <;> simp_all [readsCS]
  · split_ifs at hv <;> simp_all [readsCS]
  · simp [readsCS] at hv
theorem readsCS_mkNegC (x : CS F) : ∀ v ∈ readsCS (mkNegC x), v ∈ readsCS x := by
  intro v hv; unfold mkNegC at hv
  rcases hx : x.isKn with _ | a <;> simp only [hx] at hv
  · simpa [readsCS] using hv
  · simp [readsCS] at hv
theorem readsCS_mkPowC (x : CS F) (n : ℕ) : ∀ v ∈ readsCS (mkPowC x n), v ∈ readsCS x := by
  intro v hv; unfold mkPowC at hv
  rcases hx : x.isKn with _ | a <;> simp only [hx] at hv
  · simpa [readsCS] using hv
  · simp [readsCS] at hv

theorem readsCS_simpCS : ∀ (g : CS F), ∀ v ∈ readsCS (simpCS g), v ∈ readsCS g
  | .add a b, v, hv => by
      have := readsCS_mkAddC _ _ v hv
      simp only [List.mem_append] at this
      simp only [readsCS, List.mem_append]
      rcases this with h | h
      · exact Or.inl (readsCS_simpCS a v h)
      · exact Or.inr (readsCS_simpCS b v h)
  | .sub a b, v, hv => by
      have := readsCS_mkSubC _ _ v hv
      simp only [List.mem_append] at this
      simp only [readsCS, List.mem_append]
      rcases this with h | h
      · exact Or.inl (readsCS_simpCS a v h)
      · exact Or.inr (readsCS_simpCS b v h)
  | .mul a b, v, hv => by
      have := readsCS_mkMulC _ _ v hv
      simp only [List.mem_append] at this
      simp only [readsCS, List.mem_append]
      rcases this with h | h
      · exact Or.inl (readsCS_simpCS a v h)
      · exact Or.inr (readsCS_simpCS b v h)
  | .neg a, v, hv => by
      simp only [readsCS]; exact readsCS_simpCS a v (readsCS_mkNegC _ v hv)
  | .pow a n, v, hv => by
      simp only [readsCS]; exact readsCS_simpCS a v (readsCS_mkPowC _ n v hv)
  | .kn _, v, hv => hv | .col _ _, v, hv => hv | .opq _, v, hv => hv

/-- Reads of a binary smart constructor are reads of its arguments. -/
def ReadsSub (z x y : MS F) : Prop :=
  (∀ v ∈ kReads z, v ∈ kReads x ++ kReads y) ∧ (∀ v ∈ bReads z, v ∈ bReads x ++ bReads y)

theorem reads_mkAddM (x y : MS F) : ReadsSub (mkAddM x y) x y := by
  unfold mkAddM ReadsSub
  rcases hx : x.isCn with _ | a <;> rcases hy : y.isCn with _ | b <;> simp only
  · exact ⟨fun v hv => by simpa [kReads] using hv, fun v hv => by simpa [bReads] using hv⟩
  · split_ifs
    · exact ⟨fun v hv => by simp [hv], fun v hv => by simp [hv]⟩
    · exact ⟨fun v hv => by simpa [kReads] using hv, fun v hv => by simpa [bReads] using hv⟩
  · split_ifs
    · exact ⟨fun v hv => by simp [hv], fun v hv => by simp [hv]⟩
    · exact ⟨fun v hv => by simpa [kReads] using hv, fun v hv => by simpa [bReads] using hv⟩
  · exact ⟨fun v hv => by simp [kReads] at hv, fun v hv => by simp [bReads] at hv⟩

theorem reads_mkSubM (x y : MS F) : ReadsSub (mkSubM x y) x y := by
  unfold mkSubM ReadsSub
  rcases hx : x.isCn with _ | a <;> rcases hy : y.isCn with _ | b <;> simp only
  · exact ⟨fun v hv => by simpa [kReads] using hv, fun v hv => by simpa [bReads] using hv⟩
  · split_ifs
    · exact ⟨fun v hv => by simp [hv], fun v hv => by simp [hv]⟩
    · exact ⟨fun v hv => by simpa [kReads] using hv, fun v hv => by simpa [bReads] using hv⟩
  · exact ⟨fun v hv => by simpa [kReads] using hv, fun v hv => by simpa [bReads] using hv⟩
  · exact ⟨fun v hv => by simp [kReads] at hv, fun v hv => by simp [bReads] at hv⟩

theorem reads_mkMulM (x y : MS F) : ReadsSub (mkMulM x y) x y := by
  unfold mkMulM ReadsSub
  rcases hx : x.isCn with _ | a <;> rcases hy : y.isCn with _ | b <;> simp only
  · exact ⟨fun v hv => by simpa [kReads] using hv, fun v hv => by simpa [bReads] using hv⟩
  · split_ifs
    · exact ⟨fun v hv => by simp [kReads] at hv, fun v hv => by simp [bReads] at hv⟩
    · exact ⟨fun v hv => by simp [hv], fun v hv => by simp [hv]⟩
    · exact ⟨fun v hv => by simpa [kReads] using hv, fun v hv => by simpa [bReads] using hv⟩
  · split_ifs
    · exact ⟨fun v hv => by simp [kReads] at hv, fun v hv => by simp [bReads] at hv⟩
    · exact ⟨fun v hv => by simp [hv], fun v hv => by simp [hv]⟩
    · exact ⟨fun v hv => by simpa [kReads] using hv, fun v hv => by simpa [bReads] using hv⟩
  · exact ⟨fun v hv => by simp [kReads] at hv, fun v hv => by simp [bReads] at hv⟩

theorem reads_mkNegM (x : MS F) :
    (∀ v ∈ kReads (mkNegM x), v ∈ kReads x) ∧ (∀ v ∈ bReads (mkNegM x), v ∈ bReads x) := by
  unfold mkNegM
  rcases hx : x.isCn with _ | a <;> simp only
  · exact ⟨fun v hv => by simpa [kReads] using hv, fun v hv => by simpa [bReads] using hv⟩
  · exact ⟨fun v hv => by simp [kReads] at hv, fun v hv => by simp [bReads] at hv⟩

theorem reads_mkPowM (x : MS F) (n : ℕ) :
    (∀ v ∈ kReads (mkPowM x n), v ∈ kReads x) ∧ (∀ v ∈ bReads (mkPowM x n), v ∈ bReads x) := by
  unfold mkPowM
  rcases hx : x.isCn with _ | a <;> simp only
  · exact ⟨fun v hv => by simpa [kReads] using hv, fun v hv => by simpa [bReads] using hv⟩
  · exact ⟨fun v hv => by simp [kReads] at hv, fun v hv => by simp [bReads] at hv⟩

theorem reads_mkLift (g : CS F) :
    (∀ v ∈ kReads (mkLift g), v ∈ ([] : List (VarKind × ℕ))) ∧
      (∀ v ∈ bReads (mkLift g), v ∈ readsCS g) := by
  unfold mkLift
  rcases hg : g.isKn with _ | a <;> simp only
  · exact ⟨fun v hv => by simp [kReads] at hv, fun v hv => by simpa [bReads] using hv⟩
  · exact ⟨fun v hv => by simp [kReads] at hv, fun v hv => by simp [bReads] at hv⟩

theorem reads_mkScale (g : CS F) (u : MS F) :
    (∀ v ∈ kReads (mkScale g u), v ∈ kReads u) ∧
      (∀ v ∈ bReads (mkScale g u), v ∈ readsCS g ++ bReads u) := by
  unfold mkScale
  rcases hg : g.isKn with _ | a <;> simp only
  · exact ⟨fun v hv => by simpa [kReads] using hv, fun v hv => by simpa [bReads] using hv⟩
  · split_ifs
    · exact ⟨fun v hv => by simp [kReads] at hv, fun v hv => by simp [bReads] at hv⟩
    · exact ⟨fun v hv => hv, fun v hv => by simp [hv]⟩
    · exact ⟨fun v hv => by simpa [kReads] using hv, fun v hv => by simpa [bReads] using hv⟩

/-- Simplification never adds a read (either kind). -/
theorem reads_simpMS : ∀ (m : MS F),
    (∀ v ∈ kReads (simpMS m), v ∈ kReads m) ∧ (∀ v ∈ bReads (simpMS m), v ∈ bReads m)
  | .lift g => by
      have h := reads_mkLift (simpCS g)
      refine ⟨fun v hv => by simpa using h.1 v hv, fun v hv => ?_⟩
      simp only [bReads]; exact readsCS_simpCS g v (h.2 v hv)
  | .scale g u => by
      have ih := reads_simpMS u
      have h := reads_mkScale (simpCS g) (simpMS u)
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · simp only [kReads]; exact ih.1 v (h.1 v hv)
      · simp only [bReads, List.mem_append]
        rcases List.mem_append.mp (h.2 v hv) with h' | h'
        · exact Or.inl (readsCS_simpCS g v h')
        · exact Or.inr (ih.2 v h')
  | .add x y => by
      have hx := reads_simpMS x
      have hy := reads_simpMS y
      have h := reads_mkAddM (simpMS x) (simpMS y)
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · simp only [kReads, List.mem_append]
        rcases List.mem_append.mp (h.1 v hv) with h' | h'
        · exact Or.inl (hx.1 v h')
        · exact Or.inr (hy.1 v h')
      · simp only [bReads, List.mem_append]
        rcases List.mem_append.mp (h.2 v hv) with h' | h'
        · exact Or.inl (hx.2 v h')
        · exact Or.inr (hy.2 v h')
  | .sub x y => by
      have hx := reads_simpMS x
      have hy := reads_simpMS y
      have h := reads_mkSubM (simpMS x) (simpMS y)
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · simp only [kReads, List.mem_append]
        rcases List.mem_append.mp (h.1 v hv) with h' | h'
        · exact Or.inl (hx.1 v h')
        · exact Or.inr (hy.1 v h')
      · simp only [bReads, List.mem_append]
        rcases List.mem_append.mp (h.2 v hv) with h' | h'
        · exact Or.inl (hx.2 v h')
        · exact Or.inr (hy.2 v h')
  | .mul x y => by
      have hx := reads_simpMS x
      have hy := reads_simpMS y
      have h := reads_mkMulM (simpMS x) (simpMS y)
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · simp only [kReads, List.mem_append]
        rcases List.mem_append.mp (h.1 v hv) with h' | h'
        · exact Or.inl (hx.1 v h')
        · exact Or.inr (hy.1 v h')
      · simp only [bReads, List.mem_append]
        rcases List.mem_append.mp (h.2 v hv) with h' | h'
        · exact Or.inl (hx.2 v h')
        · exact Or.inr (hy.2 v h')
  | .neg x => by
      have hx := reads_simpMS x
      have h := reads_mkNegM (simpMS x)
      exact ⟨fun v hv => hx.1 v (h.1 v hv), fun v hv => hx.2 v (h.2 v hv)⟩
  | .pow x n => by
      have hx := reads_simpMS x
      have h := reads_mkPowM (simpMS x) n
      exact ⟨fun v hv => hx.1 v (h.1 v hv), fun v hv => hx.2 v (h.2 v hv)⟩
  | .var _ _ => ⟨fun _ h => h, fun _ h => h⟩
  | .cnst _ => ⟨fun _ h => h, fun _ h => h⟩

theorem kReads_toMS (known : VarKind → ℕ → Option ℤ) :
    ∀ (g : MixedExpr F), ∀ v ∈ kReads (toMS known g), v ∈ rawK g
  | .Var _ _, v, hv => hv
  | .Lift _, v, hv => by simp [toMS, kReads] at hv
  | .Scale _ u, v, hv => kReads_toMS known u v hv
  | .Const _, v, hv => by simp [toMS, kReads] at hv
  | .Add x y, v, hv | .Sub x y, v, hv | .Mul x y, v, hv => by
      simp only [toMS, kReads, rawK, List.mem_append] at hv ⊢
      rcases hv with h | h
      · exact Or.inl (kReads_toMS known x v h)
      · exact Or.inr (kReads_toMS known y v h)
  | .Neg x, v, hv | .Pow x _, v, hv => kReads_toMS known x v hv

theorem bReads_toMS (known : VarKind → ℕ → Option ℤ) :
    ∀ (g : MixedExpr F), ∀ v ∈ bReads (toMS known g), v ∈ rawB g
  | .Var _ _, v, hv => by simp [toMS, bReads] at hv
  | .Lift g, v, hv => readsCS_toCS known g v hv
  | .Scale g u, v, hv => by
      simp only [toMS, bReads, rawB, List.mem_append] at hv ⊢
      rcases hv with h | h
      · exact Or.inl (readsCS_toCS known g v h)
      · exact Or.inr (bReads_toMS known u v h)
  | .Const _, v, hv => by simp [toMS, bReads] at hv
  | .Add x y, v, hv | .Sub x y, v, hv | .Mul x y, v, hv => by
      simp only [toMS, bReads, rawB, List.mem_append] at hv ⊢
      rcases hv with h | h
      · exact Or.inl (bReads_toMS known x v h)
      · exact Or.inr (bReads_toMS known y v h)
  | .Neg x, v, hv | .Pow x _, v, hv => bReads_toMS known x v hv

/-! ## D. The `verify_child` cell receipts -/

section Receipts

open OptimizedMemoryGateBasis

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- Known base cells of a non-first, non-last, non-root `verify_child` row (`mopCol` order
`decompose, halt, read_root, verify_child` = columns `0..3`; masks `4`, `5`; root mask `153`). -/
def knownVC : VarKind → ℕ → Option ℤ
  | .traceCur, c =>
      if c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 4 ∨ c = 5 ∨ c = 153 then some 0
      else if c = 3 then some 1 else none
  | _, _ => none

/-- Known base cells when the SUCCESSOR row is a `verify_child` row. -/
def knownNextVC : VarKind → ℕ → Option ℤ
  | .traceNext, c => if c = 0 ∨ c = 1 ∨ c = 2 then some 0 else if c = 3 then some 1 else none
  | _, _ => none

/-- The perturbed `𝕂` roles: `pt.pw`, `pt.counts`, `lc.pw`, `lc.counts`. -/
def pertRoles : List ℕ := [3, 4, 8, 9]

/-- Their physical columns (`6 + 3r + k`). -/
def pertCols : List ℕ := [15, 16, 17, 18, 19, 20, 30, 31, 32, 33, 34, 35]

def blindL (kind : VarKind) (lk lb : List (VarKind × ℕ)) : Bool :=
  lk.all (fun v => !(decide (v.1 = kind) && pertRoles.contains v.2)) &&
    lb.all (fun v => !(decide (v.1 = kind) && pertCols.contains v.2))

def blindAt (kind : VarKind) (known : VarKind → ℕ → Option ℤ) (g : MixedExpr F) : Bool :=
  blindL kind (kReads (specM known g)) (bReads (specM known g))

/-- The cheap test: the raw gate already avoids the perturbed reads. -/
def rawBlind (kind : VarKind) (g : MixedExpr F) : Bool := blindL kind (rawK g) (rawB g)

theorem blindL_mono (kind : VarKind) {lk lb lk' lb' : List (VarKind × ℕ)}
    (hk : ∀ v ∈ lk', v ∈ lk) (hb : ∀ v ∈ lb', v ∈ lb) (h : blindL kind lk lb = true) :
    blindL kind lk' lb' = true := by
  simp only [blindL, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨fun v hv => h.1 v (hk v hv), fun v hv => h.2 v (hb v hv)⟩

theorem blindAt_of_raw (kind : VarKind) (known : VarKind → ℕ → Option ℤ) (g : MixedExpr F)
    (h : rawBlind kind g = true) : blindAt kind known g = true := by
  unfold blindAt specM
  refine blindL_mono kind (fun v hv => kReads_toMS known g v ((reads_simpMS _).1 v hv))
    (fun v hv => bReads_toMS known g v ((reads_simpMS _).2 v hv)) h

def blindFast (kind : VarKind) (known : VarKind → ℕ → Option ℤ) (g : MixedExpr F) : Bool :=
  rawBlind kind g || blindAt kind known g

theorem blindAt_of_fast (kind : VarKind) (known : VarKind → ℕ → Option ℤ) (g : MixedExpr F)
    (h : blindFast kind known g = true) : blindAt kind known g = true := by
  unfold blindFast at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact blindAt_of_raw kind known g h
  · exact h

theorem gate2_is_class3 (b : Module.Basis (Fin 3) F K) :
    (mixedTransitionGates (F := F) (K := K) b)[2]? = some (paperClassGate (K := K) (F := F) 3) :=
  rfl

theorem gate3_is_class4 (b : Module.Basis (Fin 3) F K) :
    (mixedTransitionGates (F := F) (K := K) b)[3]? = some (paperClassGate (K := K) (F := F) 4) :=
  rfl

theorem gate32_is_walkAccStep (b : Module.Basis (Fin 3) F K) :
    (mixedTransitionGates (F := F) (K := K) b)[32]? =
      some (MemoryWalkLabel.walkAccStepInGate (F := F)) :=
  rfl

set_option maxHeartbeats 8000000 in
/-- **At a non-first, non-last, non-root `verify_child` row only the class gates `q = 3, 4`
(`pt.pw`, `pt.counts`) read roles `3, 4, 8, 9` or their columns.** -/
theorem vc_cur_blind (b : Module.Basis (Fin 3) F K) :
    (mixedTransitionGates (F := F) (K := K) b).zipIdx.all
      (fun p => p.2 == 2 || p.2 == 3 || blindFast .traceCur knownVC p.1) = true := rfl

set_option maxHeartbeats 8000000 in
/-- Positive control: gate `2` (`pt.pw`) reads role `3` at that row. -/
theorem vc_cur_class3_reads (b : Module.Basis (Fin 3) F K) :
    ((mixedTransitionGates (F := F) (K := K) b).map (blindAt .traceCur knownVC)).take 4 =
      [true, true, false, false] := rfl

set_option maxHeartbeats 8000000 in
/-- **When the successor row is `verify_child`, only the walk accumulation step reads its roles
`3, 4, 8, 9` or their columns.** -/
theorem vc_next_blind (b : Module.Basis (Fin 3) F K) :
    (mixedTransitionGates (F := F) (K := K) b).zipIdx.all
      (fun p => p.2 == 32 || blindFast .traceNext knownNextVC p.1) = true := rfl

/-- Positive control: the walk accumulation step does read them. -/
theorem vc_next_walkAcc_reads :
    blindAt (F := F) .traceNext knownNextVC MemoryWalkLabel.walkAccStepInGate = false := rfl

end Receipts

end Nock.RedTeam.Batch1392

#print axioms Nock.RedTeam.Batch1392.vc_cur_blind
#print axioms Nock.RedTeam.Batch1392.vc_next_blind
#print axioms Nock.RedTeam.Batch1392.specM_eval
#print axioms Nock.RedTeam.Batch1392.evalMS_congr
#print axioms Nock.RedTeam.Batch1392.blindAt_of_fast
