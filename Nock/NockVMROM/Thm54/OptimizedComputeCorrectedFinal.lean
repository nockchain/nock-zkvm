import Nock.NockVMROM.Thm54.OptimizedComputeFinal
import Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate

/-!
# Corrected production final compute compiler
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeCorrectedFinal

set_option maxRecDepth 300000
set_option maxHeartbeats 8000000

open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Module
open OptimizedComputeBaseGates
open OptimizedComputeFinal
open OptimizedComputeFinalTypedLowering
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open scoped Polynomial

noncomputable section

inductive CorrectedFinalTypedExpr where
  | baseCur : Fin 13 → CorrectedFinalTypedExpr
  | baseNext : Fin 13 → CorrectedFinalTypedExpr
  | extCur : Fin 63 → CorrectedFinalTypedExpr
  | extNext : Fin 63 → CorrectedFinalTypedExpr
  | challenge : Fin 12 → CorrectedFinalTypedExpr
  | extensionPublic : Fin 3 → CorrectedFinalTypedExpr
  | scalarPublic : Fin 22 → CorrectedFinalTypedExpr
  | const : ℤ → CorrectedFinalTypedExpr
  | add : CorrectedFinalTypedExpr → CorrectedFinalTypedExpr → CorrectedFinalTypedExpr
  | sub : CorrectedFinalTypedExpr → CorrectedFinalTypedExpr → CorrectedFinalTypedExpr
  | mul : CorrectedFinalTypedExpr → CorrectedFinalTypedExpr → CorrectedFinalTypedExpr
  | neg : CorrectedFinalTypedExpr → CorrectedFinalTypedExpr
  | pow : CorrectedFinalTypedExpr → ℕ → CorrectedFinalTypedExpr
  /-- Form R certificate base column `202 + i` of the current row (`c_j`, `m_k`, `h`, `t`, …;
  `OptimizedComputeRangeCertificate.col0`). -/
  | certBase : Fin 94 → CorrectedFinalTypedExpr
  /-- Form R `𝕂` helper of the current row: `H` (`0`, limbs `296..298`) and `T` (`1`, limbs
  `299..301`) — `OptimizedComputeRangeCertificate.colHK` / `colTK`. -/
  | certExt : Fin 2 → CorrectedFinalTypedExpr
  /-- `λ^{(n−1) − d}` for `d ≤ n − 1` and `0` otherwise, `n − 1 = MemoryTable.pwScaleExp`,
  `λ` the `𝕂` compute challenge `9` (the Form R record slots `C'` / `λ^{n−1}`). -/
  | lamPow : Fin 64 → CorrectedFinalTypedExpr
  | expCur : CorrectedFinalTypedExpr
deriving DecidableEq

/-- Value of the `lamPow d` leaf at `λ`: `λ^{(n−1) − d}` when `d ≤ n − 1`, else `0`. -/
noncomputable def lamPowVal {K : Type*} [Field K] (lam : K) (d : ℕ) : K :=
  if d ≤ MemoryTable.pwScaleExp K then lam ^ (MemoryTable.pwScaleExp K - d) else 0

def correctedLowerFinal : Expr → Option CorrectedFinalTypedExpr
  | .Var .traceCur i =>
      if h : i < 13 then some (.baseCur ⟨i, h⟩)
      else if h : i < 76 then some (.extCur ⟨i - 13, by omega⟩)
      else if h : 202 ≤ i ∧ i < 296 then some (.certBase ⟨i - 202, by omega⟩)
      else if i = 296 then some (.certExt 0)
      else if i = 299 then some (.certExt 1)
      else if i = 302 then some .expCur
      else none
  | .Var .traceNext i =>
      if h : i < 13 then some (.baseNext ⟨i, h⟩)
      else if h : i < 76 then some (.extNext ⟨i - 13, by omega⟩) else none
  | .Var .challenge i =>
      if h : i < 12 then some (.challenge ⟨i, h⟩)
      else if h : 100 ≤ i ∧ i < 164 then some (.lamPow ⟨i - 100, by omega⟩) else none
  | .Var .publicVal i =>
      if h : i < 3 then some (.extensionPublic ⟨i, h⟩)
      else if h : 20 ≤ i ∧ i < 42 then some (.scalarPublic ⟨i - 20, by omega⟩) else none
  | .Const c => some (.const c)
  | .Add x y => return .add (← correctedLowerFinal x) (← correctedLowerFinal y)
  | .Sub x y => return .sub (← correctedLowerFinal x) (← correctedLowerFinal y)
  | .Mul x y => return .mul (← correctedLowerFinal x) (← correctedLowerFinal y)
  | .Neg x => return .neg (← correctedLowerFinal x)
  | .Pow x n => return .pow (← correctedLowerFinal x) n

def CorrectedFinalTypedExpr.degree : CorrectedFinalTypedExpr → ℕ
  | .baseCur _ | .baseNext _ | .extCur _ | .extNext _ => 1
  | .certBase _ | .certExt _ => 1
  | .expCur => 1
  | .challenge _ | .extensionPublic _ | .scalarPublic _ | .const _ => 0
  | .lamPow _ => 0
  | .add x y | .sub x y => max x.degree y.degree
  | .mul x y => x.degree + y.degree
  | .neg x => x.degree
  | .pow x n => n * x.degree

/-- Same-object semantic environment for the corrected final compiler.  Extension-valued
challenges/publics remain in `K`; the fixed selector publics remain scalars in `F`. -/
structure CorrectedFinalTypedEnv (F K : Type*) [Zero F] [Zero K] where
  baseTrace : Fin 13 → F
  baseTraceNext : Fin 13 → F
  extTrace : Fin 63 → K
  extTraceNext : Fin 63 → K
  chal : Fin 12 → K
  extensionPublic : Fin 3 → K
  scalarPublic : Fin 22 → F
  /-- Form R certificate base columns `202.. 295` of the current row. -/
  certBase : Fin 94 → F := fun _ => 0
  /-- Form R `𝕂` helpers `H` (`0`) and `T` (`1`) of the current row. -/
  certExt : Fin 2 → K := fun _ => 0
  /-- The successor row's certificate base columns (read only through `traceNext`). -/
  certBaseNext : Fin 94 → F := fun _ => 0
  /-- The successor row's `𝕂` helpers (read only through `traceNext`). -/
  certExtNext : Fin 2 → K := fun _ => 0
  expCol : F := 0
  /-- The successor row's carrier (read only through `traceNext`). -/
  expColNext : F := 0

def CorrectedFinalTypedExpr.eval
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) : CorrectedFinalTypedExpr → K
  | .baseCur i => algebraMap F K (env.baseTrace i)
  | .baseNext i => algebraMap F K (env.baseTraceNext i)
  | .extCur i => env.extTrace i
  | .extNext i => env.extTraceNext i
  | .challenge i => env.chal i
  | .extensionPublic i => env.extensionPublic i
  | .scalarPublic i => algebraMap F K (env.scalarPublic i)
  | .const c => c
  | .add x y => x.eval env + y.eval env
  | .sub x y => x.eval env - y.eval env
  | .mul x y => x.eval env * y.eval env
  | .neg x => -x.eval env
  | .pow x n => (x.eval env) ^ n
  | .certBase i => algebraMap F K (env.certBase i)
  | .certExt i => env.certExt i
  | .lamPow d => lamPowVal (env.chal 9) d
  | .expCur => algebraMap F K env.expCol

/-- Mixed source environment represented by one corrected typed environment. -/
def CorrectedFinalTypedEnv.toSourceEnv
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) : Env K where
  trace i :=
    if h : i < 13 then algebraMap F K (env.baseTrace ⟨i, h⟩)
    else if h : i < 76 then env.extTrace ⟨i - 13, by omega⟩
    else if h : 202 ≤ i ∧ i < 296 then algebraMap F K (env.certBase ⟨i - 202, by omega⟩)
    else if i = 296 then env.certExt 0
    else if i = 299 then env.certExt 1
    else if i = 302 then algebraMap F K env.expCol
    else 0
  traceNext i :=
    if h : i < 13 then algebraMap F K (env.baseTraceNext ⟨i, h⟩)
    else if h : i < 76 then env.extTraceNext ⟨i - 13, by omega⟩
    else if h : 202 ≤ i ∧ i < 296 then algebraMap F K (env.certBaseNext ⟨i - 202, by omega⟩)
    else if i = 296 then env.certExtNext 0
    else if i = 299 then env.certExtNext 1
    else if i = 302 then algebraMap F K env.expColNext
    else 0
  chal i :=
    if h : i < 12 then env.chal ⟨i, h⟩
    else if 100 ≤ i ∧ i < 164 then lamPowVal (env.chal 9) (i - 100)
    else 0
  pub i :=
    if h : i < 3 then env.extensionPublic ⟨i, h⟩
    else if h : 20 ≤ i ∧ i < 42 then
      algebraMap F K (env.scalarPublic ⟨i - 20, by omega⟩)
    else 0

theorem correctedLowerFinal_eval
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) (e : Expr) (t : CorrectedFinalTypedExpr)
    (h : correctedLowerFinal e = some t) :
    e.eval env.toSourceEnv = t.eval env := by
  induction e generalizing t with
  | Var kind i =>
      cases kind
      · by_cases h13 : i < 13
        · simp [correctedLowerFinal, h13] at h
          subst t
          simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
            CorrectedFinalTypedExpr.eval, h13]
        · by_cases h76 : i < 76
          · simp [correctedLowerFinal, h13, h76] at h
            subst t
            simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
              CorrectedFinalTypedExpr.eval, h13, h76]
          · by_cases hc : 202 ≤ i ∧ i < 296
            · simp [correctedLowerFinal, h13, h76, hc] at h
              subst t
              simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
                CorrectedFinalTypedExpr.eval, h13, h76, hc]
            · by_cases h296 : i = 296
              · subst h296
                simp [correctedLowerFinal] at h
                subst t
                simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
                  CorrectedFinalTypedExpr.eval]
              · by_cases h299 : i = 299
                · subst h299
                  simp [correctedLowerFinal] at h
                  subst t
                  simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
                    CorrectedFinalTypedExpr.eval]
                · by_cases h302 : i = 302
                  · subst h302
                    simp [correctedLowerFinal] at h
                    subst t
                    simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
                      CorrectedFinalTypedExpr.eval]
                  · simp [correctedLowerFinal, h13, h76, hc, h296, h299, h302] at h
      · by_cases h13 : i < 13
        · simp [correctedLowerFinal, h13] at h
          subst t
          simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
            CorrectedFinalTypedExpr.eval, h13]
        · by_cases h76 : i < 76
          · simp [correctedLowerFinal, h13, h76] at h
            subst t
            simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
              CorrectedFinalTypedExpr.eval, h13, h76]
          · simp [correctedLowerFinal, h13, h76] at h
      · by_cases h12 : i < 12
        · simp [correctedLowerFinal, h12] at h
          subst t
          simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
            CorrectedFinalTypedExpr.eval, h12]
        · by_cases hl : 100 ≤ i ∧ i < 164
          · simp [correctedLowerFinal, h12, hl] at h
            subst t
            simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
              CorrectedFinalTypedExpr.eval, h12, hl]
          · simp [correctedLowerFinal, h12, hl] at h
      · by_cases h2 : i < 3
        · simp [correctedLowerFinal, h2] at h
          subst t
          simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
            CorrectedFinalTypedExpr.eval, h2]
        · by_cases hs : 20 ≤ i ∧ i < 42
          · simp [correctedLowerFinal, h2, hs] at h
            subst t
            simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
              CorrectedFinalTypedExpr.eval, h2, hs]
          · simp [correctedLowerFinal, h2, hs] at h
  | Const c =>
      simp only [correctedLowerFinal, Option.some.injEq] at h
      subst t
      simp [Expr.eval, CorrectedFinalTypedExpr.eval]
  | Add x y ihx ihy =>
      cases hx : correctedLowerFinal x with
      | none => simp [correctedLowerFinal, hx] at h
      | some tx =>
          cases hy : correctedLowerFinal y with
          | none => simp [correctedLowerFinal, hx, hy] at h
          | some ty =>
              simp [correctedLowerFinal, hx, hy] at h
              subst t
              simp [Expr.eval, CorrectedFinalTypedExpr.eval, ihx tx hx, ihy ty hy]
  | Sub x y ihx ihy =>
      cases hx : correctedLowerFinal x with
      | none => simp [correctedLowerFinal, hx] at h
      | some tx =>
          cases hy : correctedLowerFinal y with
          | none => simp [correctedLowerFinal, hx, hy] at h
          | some ty =>
              simp [correctedLowerFinal, hx, hy] at h
              subst t
              simp [Expr.eval, CorrectedFinalTypedExpr.eval, ihx tx hx, ihy ty hy]
  | Mul x y ihx ihy =>
      cases hx : correctedLowerFinal x with
      | none => simp [correctedLowerFinal, hx] at h
      | some tx =>
          cases hy : correctedLowerFinal y with
          | none => simp [correctedLowerFinal, hx, hy] at h
          | some ty =>
              simp [correctedLowerFinal, hx, hy] at h
              subst t
              simp [Expr.eval, CorrectedFinalTypedExpr.eval, ihx tx hx, ihy ty hy]
  | Neg x ih =>
      cases hx : correctedLowerFinal x with
      | none => simp [correctedLowerFinal, hx] at h
      | some tx =>
          simp [correctedLowerFinal, hx] at h
          subst t
          simp [Expr.eval, CorrectedFinalTypedExpr.eval, ih tx hx]
  | Pow x n ih =>
      cases hx : correctedLowerFinal x with
      | none => simp [correctedLowerFinal, hx] at h
      | some tx =>
          simp [correctedLowerFinal, hx] at h
          subst t
          simp [Expr.eval, CorrectedFinalTypedExpr.eval, ih tx hx]

def correctedFinalExtCoordIndex {e : ℕ} (i : Fin 63) (k : Fin e) : ℕ :=
  13 + e * (i : ℕ) + (k : ℕ)

def correctedFinalTypedCompile {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) : CorrectedFinalTypedExpr → Fin e → CoeffExpr F
  | .baseCur i => fun k => .mul (.var .traceCur i) (.const (coord b (1 : K) k))
  | .baseNext i => fun k => .mul (.var .traceNext i) (.const (coord b (1 : K) k))
  | .extCur i => fun k => .var .traceCur (correctedFinalExtCoordIndex i k)
  | .extNext i => fun k => .var .traceNext (correctedFinalExtCoordIndex i k)
  | .challenge i => fun k => .var .challenge (e * (i : ℕ) + (k : ℕ))
  | .extensionPublic i => fun k => .var .publicVal (e * (i : ℕ) + (k : ℕ))
  | .scalarPublic i => fun k =>
      .mul (.var .publicVal (20 + (i : ℕ))) (.const (coord b (1 : K) k))
  | .const c => fun k => .const ((c : F) * coord b (1 : K) k)
  | .add x y => fun k => .add (correctedFinalTypedCompile b x k)
      (correctedFinalTypedCompile b y k)
  | .sub x y => fun k => .sub (correctedFinalTypedCompile b x k)
      (correctedFinalTypedCompile b y k)
  | .neg x => fun k => .neg (correctedFinalTypedCompile b x k)
  | .mul x y => mulVec b (correctedFinalTypedCompile b x) (correctedFinalTypedCompile b y)
  | .pow x n => powVec b (correctedFinalTypedCompile b x) n
  | .certBase i => fun k => .mul (.var .traceCur (202 + (i : ℕ))) (.const (coord b (1 : K) k))
  | .certExt i => fun k => .var .traceCur (296 + e * (i : ℕ) + (k : ℕ))
  | .lamPow d => fun k =>
      if (d : ℕ) ≤ MemoryTable.pwScaleExp K then
        powVec b (fun k' => .var .challenge (e * 9 + (k' : ℕ))) (MemoryTable.pwScaleExp K - d) k
      else .const 0
  | .expCur => fun k => .mul (.var .traceCur 302) (.const (coord b (1 : K) k))

/-- Coordinate relation between one same-object typed environment and the physical base-field
environment consumed by the corrected compiler. -/
structure IsCorrectedFinalCoordEnv
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K)
    (env : CorrectedFinalTypedEnv F K) (envF : Env F) : Prop where
  baseTrace : ∀ i : Fin 13, envF.trace i = env.baseTrace i
  baseTraceNext : ∀ i : Fin 13, envF.traceNext i = env.baseTraceNext i
  extTrace : ∀ (i : Fin 63) (k : Fin e),
    envF.trace (correctedFinalExtCoordIndex i k) = coord b (env.extTrace i) k
  extTraceNext : ∀ (i : Fin 63) (k : Fin e),
    envF.traceNext (correctedFinalExtCoordIndex i k) = coord b (env.extTraceNext i) k
  chal : ∀ (i : Fin 12) (k : Fin e),
    envF.chal (e * (i : ℕ) + (k : ℕ)) = coord b (env.chal i) k
  extensionPublic : ∀ (i : Fin 3) (k : Fin e),
    envF.pub (e * (i : ℕ) + (k : ℕ)) = coord b (env.extensionPublic i) k
  scalarPublic : ∀ i : Fin 22, envF.pub (20 + (i : ℕ)) = env.scalarPublic i
  certBase : ∀ i : Fin 94, envF.trace (202 + (i : ℕ)) = env.certBase i
  certExt : ∀ (i : Fin 2) (k : Fin e),
    envF.trace (296 + e * (i : ℕ) + (k : ℕ)) = coord b (env.certExt i) k
  expCol : envF.trace 302 = env.expCol

theorem correctedFinalTypedCompile_eval
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {e : ℕ} (b : Basis (Fin e) F K)
    (env : CorrectedFinalTypedEnv F K) (envF : Env F)
    (henv : IsCorrectedFinalCoordEnv b env envF)
    (t : CorrectedFinalTypedExpr) (k : Fin e) :
    coord b (t.eval env) k = (correctedFinalTypedCompile b t k).eval envF := by
  induction t generalizing k with
  | baseCur i =>
      simp only [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval]
      rw [show algebraMap F K (env.baseTrace i) = env.baseTrace i • (1 : K) by
        simp [Algebra.smul_def], coord_smul, henv.baseTrace]
      simp [smul_eq_mul]
  | baseNext i =>
      simp only [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval]
      rw [show algebraMap F K (env.baseTraceNext i) = env.baseTraceNext i • (1 : K) by
        simp [Algebra.smul_def], coord_smul, henv.baseTraceNext]
      simp [smul_eq_mul]
  | extCur i =>
      simpa [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval] using
        (henv.extTrace i k).symm
  | extNext i =>
      simpa [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval] using
        (henv.extTraceNext i k).symm
  | challenge i =>
      simpa [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval] using
        (henv.chal i k).symm
  | extensionPublic i =>
      simpa [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval] using
        (henv.extensionPublic i k).symm
  | scalarPublic i =>
      simp only [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval]
      rw [show algebraMap F K (env.scalarPublic i) = env.scalarPublic i • (1 : K) by
        simp [Algebra.smul_def], coord_smul, henv.scalarPublic]
      simp [smul_eq_mul]
  | const c => exact coord_intCast b c k
  | add x y ihx ihy =>
      simp only [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval,
        coord_add, ihx, ihy]
  | sub x y ihx ihy =>
      simp only [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval,
        coord_sub, ihx, ihy]
  | neg x ih =>
      simp only [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval,
        coord_neg, ih]
  | mul x y ihx ihy =>
      exact eval_mulVec b envF _ _ (x.eval env) (y.eval env) ihx ihy k
  | pow x n ih =>
      exact eval_powVec b envF _ (x.eval env) ih n k
  | certBase i =>
      simp only [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval]
      rw [show algebraMap F K (env.certBase i) = env.certBase i • (1 : K) by
        simp [Algebra.smul_def], coord_smul, henv.certBase]
      simp [smul_eq_mul]
  | certExt i =>
      simpa [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval] using
        (henv.certExt i k).symm
  | lamPow d =>
      simp only [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, lamPowVal]
      split_ifs with hd
      · exact eval_powVec b envF _ (env.chal 9)
          (fun k' => by simpa [CoeffExpr.eval] using (henv.chal 9 k').symm) _ k
      · simp [coord_zero, CoeffExpr.eval]
  | expCur =>
      simp only [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval]
      rw [show algebraMap F K env.expCol = env.expCol • (1 : K) by
        simp [Algebra.smul_def], coord_smul, henv.expCol]
      simp [smul_eq_mul]

theorem correctedFinalTypedCompile_zero_iff
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {e : ℕ} (b : Basis (Fin e) F K)
    (env : CorrectedFinalTypedEnv F K) (envF : Env F)
    (henv : IsCorrectedFinalCoordEnv b env envF)
    (t : CorrectedFinalTypedExpr) :
    (∀ k, (correctedFinalTypedCompile b t k).eval envF = 0) ↔ t.eval env = 0 := by
  constructor
  · intro h
    rw [eq_iff_coords_eq b (t.eval env) 0]
    intro k
    rw [coord_zero, correctedFinalTypedCompile_eval b env envF henv]
    exact h k
  · intro h k
    rw [← correctedFinalTypedCompile_eval b env envF henv, h, coord_zero]

theorem correctedFinalTypedCompile_degree_le
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) (t : CorrectedFinalTypedExpr) (k : Fin e) :
    (correctedFinalTypedCompile b t k).degree ≤ t.degree := by
  induction t generalizing k with
  | baseCur i => simp [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
  | baseNext i => simp [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
  | extCur i => simp [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
  | extNext i => simp [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
  | challenge i =>
      simp [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
  | extensionPublic i =>
      simp [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
  | scalarPublic i =>
      simp [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
  | const i => simp [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
  | add x y ihx ihy =>
      simp only [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
      exact max_le_max (ihx k) (ihy k)
  | sub x y ihx ihy =>
      simp only [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
      exact max_le_max (ihx k) (ihy k)
  | neg x ih =>
      simpa [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree] using ih k
  | mul x y ihx ihy => exact degree_mulVec_le b _ _ x.degree y.degree ihx ihy k
  | pow x n ih => exact degree_powVec_le b _ x.degree ih n k
  | certBase i =>
      simp [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
  | certExt i =>
      simp [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
  | lamPow d =>
      simp only [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree]
      split_ifs
      · simpa using degree_powVec_le b (fun k' => (.var .challenge (e * 9 + (k' : ℕ)) :
          CoeffExpr F)) 0 (fun _ => by simp [CoeffExpr.degree]) _ k
      · simp [CoeffExpr.degree]
  | expCur =>
      simp [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]

def correctedLoweredExt : List CorrectedFinalTypedExpr :=
  finalExtTransitionGates.filterMap correctedLowerFinal

/-- **`isFirst · acc = 0`** — the request accumulator starts at zero.  A-comp
anchoring stage.  The accumulator is extension role `32` (raw `45`). -/
def finalAccInit : Expr := .Mul OptimizedComputeTemplate.fixedIsFirst (.Var .traceCur 45)

/-- **`isLast · (acc_after − requests) = 0`** — the paper's terminal constraint
`requests = acc_prog(h₁)`, against the post-challenge public `requests`
(`𝕂` public role `2`, base publics `6..8`; shared with the memory chip per `:597`).
`acc_after` is witness role `60` (raw `73`). -/
def finalAccTerminal : Expr :=
  .Mul OptimizedComputeTemplate.fixedIsLast (.Sub (.Var .traceCur OptimizedComputeFiniteIOGates.accAfterIndex)
    (.Var .publicVal 2))

/-- `ln_prev` is `W_comp`'s first witness column,
extension role `54` (raw `67`, `OptimizedComputeSubstitution.lnPrev`); the timestamp of the
`j`-th request of row `i` is decoded as `ln_prev(i) · α^{j+1}` and the
paper's uniqueness argument needs `ln_prev(0) = 1` — the row-`0` count of "memory
accesses requested until that row" (`:1884`).  The honest generator renders
`ln_prev = α ^ lnPrevExponent` with the first exponent `0` (`Gen.lean` `renderOp*Row`,
`ComputeLineStartsAtZero`), so the honest value is `α^0 = 1` for every generated execution and
every `α`, `α = 0` included. -/
def finalLnInit : Expr :=
  .Mul OptimizedComputeTemplate.fixedIsFirst
    (.Sub (OptimizedComputeSubstitution.lnPrev .traceCur) (.Const 1))

def correctedEndpoint2 : List CorrectedFinalTypedExpr :=
  [finalMaskedWalkLn1, finalMaskedWalkCount1, finalMaskedWalkOut, finalAccInit, finalAccTerminal,
    finalLnInit].filterMap correctedLowerFinal

def correctedEndpoint4 : List CorrectedFinalTypedExpr :=
  [finalMaskedWalkAccInit].filterMap correctedLowerFinal

theorem corrected_lowered_counts :
    correctedLoweredExt.length = 82 ∧ correctedEndpoint2.length = 6 ∧
      correctedEndpoint4.length = 1 := by
  set_option maxRecDepth 300000 in decide

/-- If `filterMap f` preserves length, `f` is total on `l` and `get` commutes with it. -/
theorem get_filterMap_of_length_eq {α β : Type*} (f : α → Option β) :
    ∀ (l : List α) (hlen : (l.filterMap f).length = l.length)
      (i : ℕ) (hi : i < l.length),
        f (l.get ⟨i, hi⟩) =
          some ((l.filterMap f).get ⟨i, Nat.lt_of_lt_of_eq hi hlen.symm⟩) := by
  intro l hlen i hi
  induction l generalizing i with
  | nil => cases hi
  | cons a t ih =>
    cases hf : f a with
    | none =>
      have : (t.filterMap f).length ≤ t.length := List.length_filterMap_le f t
      simp [List.filterMap, hf] at hlen
      omega
    | some b =>
      have hfmap : (a :: t).filterMap f = b :: t.filterMap f := by
        simp [List.filterMap, hf]
      have hlen' : (t.filterMap f).length = t.length := by
        rw [hfmap, List.length_cons, List.length_cons] at hlen
        exact Nat.succ_injective hlen
      cases i with
      | zero =>
        simp [hf, List.filterMap]
      | succ n =>
        have hn : n < t.length := Nat.succ_lt_succ_iff.mp hi
        have ih' := ih hlen' n hn
        simpa [List.get_cons_succ, hf, List.filterMap] using ih'

theorem corrected_lowered_degrees :
    (∀ t ∈ correctedLoweredExt, t.degree ≤ 4) ∧
      (∀ t ∈ correctedEndpoint2, t.degree ≤ 2) ∧
      (∀ t ∈ correctedEndpoint4, t.degree ≤ 4) := by
  set_option maxRecDepth 300000 in decide

def correctedCompileList {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (ts : List CorrectedFinalTypedExpr) : List (CoeffExpr F) :=
  ts.flatMap fun t => List.ofFn fun k : Fin 3 => correctedFinalTypedCompile b t k

@[simp] theorem correctedCompileList_length
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (ts : List CorrectedFinalTypedExpr) :
    (correctedCompileList b ts).length = ts.length * 3 := by simp [correctedCompileList]

theorem correctedCompileList_degree
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (ts : List CorrectedFinalTypedExpr) (d : ℕ)
    (hdeg : ∀ t ∈ ts, t.degree ≤ d) :
    ∀ g ∈ correctedCompileList b ts, g.degree ≤ d := by
  intro g hg
  rw [correctedCompileList] at hg
  obtain ⟨xs, hxs, hg⟩ := List.mem_flatten.mp hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hxs
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
  exact (correctedFinalTypedCompile_degree_le b t k).trans (hdeg t ht)

abbrev CorrectedCoreExtGateId := Fin 82
abbrev CorrectedResidualWitnessId := Fin 3

/-- Residual witness roles `58, 59` in the Fin 63 production extension (role `60` is
`acc_after`, not a residual). -/
def residualWitnessRole (j : CorrectedResidualWitnessId) : Fin 63 :=
  ⟨58 + (j : ℕ), by omega⟩

/-- F-E-2: notLast-masked / residual-witnessed,
never unmasked at the terminal row. -/
abbrev packedLnChainId : CorrectedCoreExtGateId := ⟨72, by omega⟩
abbrev packedWalkLnId : CorrectedCoreExtGateId := ⟨73, by omega⟩
abbrev packedWalkCountId : CorrectedCoreExtGateId := ⟨74, by omega⟩
abbrev packedWalkAccId : CorrectedCoreExtGateId := ⟨75, by omega⟩
abbrev packedQueueNonEmptyId : CorrectedCoreExtGateId := ⟨76, by omega⟩
abbrev packedQueueTilingId : CorrectedCoreExtGateId := ⟨77, by omega⟩
abbrev packedChainId : CorrectedCoreExtGateId := ⟨81, by omega⟩
def packedLnChainIdx : ℕ := packedLnChainId.val
def packedWalkLnIdx : ℕ := packedWalkLnId.val
def packedWalkCountIdx : ℕ := packedWalkCountId.val
def packedWalkAccIdx : ℕ := packedWalkAccId.val
def packedChainIdx : ℕ := packedChainId.val

def correctedFinalExtGate (i : CorrectedCoreExtGateId) : CorrectedFinalTypedExpr :=
  correctedLoweredExt.get ⟨i, by rw [corrected_lowered_counts.1]; exact i.isLt⟩

theorem correctedLoweredExt_length_eq_source :
    (finalExtTransitionGates.filterMap correctedLowerFinal).length =
      finalExtTransitionGates.length := by
  rw [show (finalExtTransitionGates.filterMap correctedLowerFinal).length =
      correctedLoweredExt.length from rfl, corrected_lowered_counts.1,
    finalExtTransitionGates_length]

theorem correctedFinalExtGate_of_lower (i : CorrectedCoreExtGateId) :
    correctedLowerFinal (finalExtTransitionGates.get ⟨i, by simp⟩) =
      some (correctedFinalExtGate i) := by
  have hlen := correctedLoweredExt_length_eq_source
  have hi : (i : ℕ) < finalExtTransitionGates.length := by simp
  have hget := get_filterMap_of_length_eq correctedLowerFinal
    finalExtTransitionGates hlen (i : ℕ) hi
  simpa [correctedFinalExtGate, correctedLoweredExt] using hget

theorem correctedFinalExtGate_eval_source
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) (i : CorrectedCoreExtGateId) :
    (finalExtTransitionGates.get ⟨i, by simp⟩).eval env.toSourceEnv =
      (correctedFinalExtGate i).eval env :=
  correctedLowerFinal_eval env _ _ (correctedFinalExtGate_of_lower i)

def correctedFinalResidualSource : CorrectedResidualWitnessId → CorrectedFinalTypedExpr
  | 0 => correctedFinalExtGate packedWalkCountId
  | 1 => correctedFinalExtGate packedWalkAccId
  | 2 => correctedFinalExtGate packedChainId

/-! ### The anchored IO accumulator: witness role `60` is `acc_after`

Until
this stage witness role `60` was the sampled-IO fold's *residual* — `aux[2] = w₆₀ − fold`,
`core[20] = (1 − last)·w₆₀` — so the accumulator (role `32`) was constrained only through its
per-row increments and anchored at neither end.  Now:

* `aux[2]` is the **unmasked** step `correctedAccAfterStep`, the paper's the paper
  transition with `acc_prog(i)` read from role `60` of the *same* row, valid at the last row;
* the endpoints `isFirst · acc = 0` and `isLast · (acc_after − requests) = 0` join `correctedEndpoint2` in increment 3.

`w = 199` is unchanged: no column is added, one is re-purposed. -/

/-- The unmasked accumulator step in the production namespace. -/
def finalAccAfterStep : Expr :=
  OptimizedComputeFiniteIOGates.optimizedAccAfterStep.subst finalSampledNamespace

/-- Typed form of `finalAccAfterStep`; the lowering is total on it (`correctedLowerFinal_accAfterStep`). -/
def correctedAccAfterStep : CorrectedFinalTypedExpr :=
  (correctedLowerFinal finalAccAfterStep).getD (.const 0)

theorem correctedLowerFinal_accAfterStep :
    correctedLowerFinal finalAccAfterStep = some correctedAccAfterStep := by
  set_option maxRecDepth 300000 in decide

theorem correctedAccAfterStep_degree : correctedAccAfterStep.degree ≤ 4 := by
  set_option maxRecDepth 300000 in decide

/-- Chain gate: off the last row, this row's `acc_after` (role `60`) is the next row's
accumulator (role `32`).  Twin of `OptimizedMemoryGateBasis.accChainMixed`. -/
def accAfterChain : CorrectedFinalTypedExpr :=
  .mul (.sub (.const 1) (.baseCur 12)) (.sub (.extCur 60) (.extNext 32))

theorem accAfterChain_degree : accAfterChain.degree ≤ 2 := by decide

/-- Raw index of `acc_after` is extension role `60`, and the accumulator is role `32`
(`overlayCoord _ 5 = pubFP _ 10 2`, raw `45`). -/
theorem accAfter_roles :
    OptimizedComputeFiniteIOGates.accAfterIndex = 13 + 60 ∧
      (correctedLowerFinal (.Var .traceCur OptimizedComputeFiniteIOGates.accAfterIndex) =
        some (.extCur 60)) ∧
      correctedLowerFinal (sampledIOSubst .traceNext 0) = some (.extNext 32) := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

def correctedCoreCoord {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (i : CorrectedCoreExtGateId) (k : Fin 3) : CoeffExpr F :=
  if i = packedWalkCountId then .mul notLastCoeff (residualWitnessCoord 0 k)
  else if i = packedWalkAccId then .mul notLastCoeff (residualWitnessCoord 1 k)
  else if i = packedChainId then correctedFinalTypedCompile b accAfterChain k
  else if i = packedLnChainId ∨ i = packedWalkLnId then
    .mul notLastCoeff (correctedFinalTypedCompile b (correctedFinalExtGate i) k)
  else correctedFinalTypedCompile b (correctedFinalExtGate i) k

def correctedAuxCoord {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (j : CorrectedResidualWitnessId) (k : Fin 3) : CoeffExpr F :=
  if j = 2 then correctedFinalTypedCompile b correctedAccAfterStep k
  else
    .sub (residualWitnessCoord j k)
      (correctedFinalTypedCompile b (correctedFinalResidualSource j) k)

def correctedCore {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  (List.ofFn fun i : CorrectedCoreExtGateId =>
    List.ofFn fun k : Fin 3 => correctedCoreCoord b i k).flatten

def correctedAux {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  (List.ofFn fun j : CorrectedResidualWitnessId =>
    List.ofFn fun k : Fin 3 => correctedAuxCoord b j k).flatten

theorem correctedCoreCoord_degree
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (i : CorrectedCoreExtGateId) (k : Fin 3) :
    (correctedCoreCoord b i k).degree ≤ 4 := by
  by_cases h10 : i = packedWalkCountId
  · subst i
    simp [correctedCoreCoord, packedWalkCountId, packedWalkAccId, packedChainId,
      packedLnChainId, packedWalkLnId, notLastCoeff, residualWitnessCoord, isLastVar, bv,
      CoeffExpr.degree]
  by_cases h11 : i = packedWalkAccId
  · subst i
    simp [correctedCoreCoord, packedWalkCountId, packedWalkAccId, packedChainId,
      packedLnChainId, packedWalkLnId, notLastCoeff, residualWitnessCoord, isLastVar, bv,
      CoeffExpr.degree]
  by_cases h20 : i = packedChainId
  · subst i
    simp only [correctedCoreCoord, packedWalkCountId, packedWalkAccId, packedChainId,
      packedLnChainId, packedWalkLnId, if_pos rfl, h10, h11, if_false]
    exact (correctedFinalTypedCompile_degree_le b _ k).trans
      (accAfterChain_degree.trans (by norm_num))
  by_cases hs : i = packedLnChainId ∨ i = packedWalkLnId
  · have ht : (correctedFinalTypedCompile b (correctedFinalExtGate i) k).degree ≤ 3 := by
      rcases hs with h | h <;> subst i <;>
        exact (correctedFinalTypedCompile_degree_le b _ k).trans (by decide)
    simp only [correctedCoreCoord, packedWalkCountId, packedWalkAccId, packedChainId,
      packedLnChainId, packedWalkLnId, h10, h11, h20, hs, if_false, if_true, CoeffExpr.degree]
    exact Nat.add_le_add
      (by simp [notLastCoeff, isLastVar, bv, CoeffExpr.degree]) ht
  · simp only [correctedCoreCoord, packedWalkCountId, packedWalkAccId, packedChainId,
      packedLnChainId, packedWalkLnId, h10, h11, h20, hs, if_false]
    exact (correctedFinalTypedCompile_degree_le b _ k).trans
      (corrected_lowered_degrees.1 _ (List.get_mem _ _))

theorem correctedAuxCoord_degree
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (j : CorrectedResidualWitnessId) (k : Fin 3) :
    (correctedAuxCoord b j k).degree ≤ 4 := by
  by_cases h2 : j = 2
  · subst j
    simp only [correctedAuxCoord, if_pos rfl]
    exact (correctedFinalTypedCompile_degree_le b _ k).trans correctedAccAfterStep_degree
  have hs : (correctedFinalResidualSource j).degree ≤ 4 := by
    fin_cases j <;> first | decide | exact absurd rfl h2
  simp only [correctedAuxCoord, h2, if_false, CoeffExpr.degree]
  exact max_le (by simp [residualWitnessCoord, CoeffExpr.degree])
    ((correctedFinalTypedCompile_degree_le b _ k).trans hs)


/-- `1 + m_k (λ^{2^k} − 1)`, `m_k` the certificate shift bit at column `202 + 63 + k`. -/
def formRLamFactor (k : Fin 6) : CorrectedFinalTypedExpr :=
  .add (.const 1)
    (.mul (.certBase ⟨63 + (k : ℕ), by omega⟩)
      (.sub (.pow (.challenge 9) (2 ^ (k : ℕ))) (.const 1)))

/-- `H − Π_{k<3}(1 + m_k(λ^{2^k} − 1))`. -/
def formRLamHPin : CorrectedFinalTypedExpr :=
  .sub (.certExt 0) (.mul (.mul (formRLamFactor 0) (formRLamFactor 1)) (formRLamFactor 2))

/-- `T − H·Π_{3≤k<6}(1 + m_k(λ^{2^k} − 1))`. -/
def formRLamTPin : CorrectedFinalTypedExpr :=
  .sub (.certExt 1)
    (.mul (.mul (.mul (.certExt 0) (formRLamFactor 3)) (formRLamFactor 4)) (formRLamFactor 5))

def formRLamPins : List CorrectedFinalTypedExpr := [formRLamHPin, formRLamTPin]

theorem formRLamPins_degree : ∀ t ∈ formRLamPins, t.degree ≤ 4 := by decide

/-! One round-0 base-field column `S` (physical column `302`, appended after the Form R `𝕂` helpers
`296..301`; no role moves).  Honest value `prefixExp`: `S(i) = Σ_{i' < i} arity(i')`, so the
`j`-th request of row `i` has exponent `S(i) + j + 1`.  Two base gates:
`isFirst · S = 0` and `(1 − isLast)·(S(i+1) − S(i) − arity(i)) = 0`, with `arity` the linear form
`Σ_s arity(s)·sel_s` in the state selectors (columns `0..10`).  Both are degree-1 bodies under a
preprocessing mask (trace degree `2 ≤ d = 4`).  **Deviation (recorded):** the paper commits no
exponent before `α`. -/

/-- Physical base column of the compute exponent carrier `S`. -/
def computeExpCol : ℕ := 302

theorem computeExpCol_eq : computeExpCol = 302 := rfl

/-- `arity(s)` per selector column: columns `0..9` are `s0..s9`, column
`10` is `cons`. -/
def arityCoeff : ℕ → ℕ
  | 0 => 2 | 1 => 1 | 2 => 2 | 3 => 1 | 4 => 1 | 5 => 2 | 6 => 3 | 7 => 2 | 8 => 2 | 9 => 3
  | _ => 1

/-- `arity(i) = Σ_{s} arity(s) · sel_s(i)`, the linear form in the eleven state selectors. -/
def arityForm {F : Type*} [Field F] : CoeffExpr F :=
  (List.range 11).foldr
    (fun c acc => .add (.mul (.const ((arityCoeff c : ℕ) : F)) (.var .traceCur c)) acc)
    (.const 0)

/-- **`isFirst · S = 0`** — the carrier starts at `0` (`isFirst` is preprocessing column `11`). -/
def expInitGate {F : Type*} [Field F] : CoeffExpr F :=
  .mul (.var .traceCur 11) (.var .traceCur computeExpCol)

/-- **`(1 − isLast)·(S(i+1) − S(i) − arity(i)) = 0`** — the running sum of the request arities
(`isLast` is preprocessing column `12`; the last row has no successor). -/
def expStepGate {F : Type*} [Field F] : CoeffExpr F :=
  .mul (.sub (.const 1) (.var .traceCur 12))
    (.sub (.sub (.var .traceNext computeExpCol) (.var .traceCur computeExpCol)) arityForm)

/-- The two carrier gates, appended to the deployed compute gate list. -/
def computeExpGates {F : Type*} [Field F] : List (CoeffExpr F) := [expInitGate, expStepGate]

theorem arityForm_degree {F : Type*} [Field F] : (arityForm (F := F)).degree ≤ 1 := by
  simp [arityForm, List.range, List.range.loop, CoeffExpr.degree]

/-- Both carrier gates are a degree-`1` body under a preprocessing mask (trace degree `2`). -/
theorem computeExpGates_degree {F : Type*} [Field F] :
    ∀ g ∈ computeExpGates (F := F), g.degree ≤ 2 := by
  intro g hg
  simp only [computeExpGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · simp [expInitGate, CoeffExpr.degree]
  · have h := arityForm_degree (F := F)
    simp only [expStepGate, CoeffExpr.degree]
    omega

@[simp] theorem computeExpGates_length {F : Type*} [Field F] :
    (computeExpGates (F := F)).length = 2 := rfl

def correctedFinalComputeAllGates {F K : Type*} [Field F] [Field K] [Algebra F K]
    (n : ℕ) (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  finalBaseTransitionGates n ++ correctedCore b ++ correctedAux b ++
    correctedCompileList b correctedEndpoint2 ++ correctedCompileList b correctedEndpoint4 ++
    finalEndpointEqualityChecks ++ formRCertificateGates (F := F) ++
    correctedCompileList b formRLamPins ++ computeExpGates (F := F)

@[simp] theorem correctedFinalComputeAllGates_length
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (n : ℕ) (b : Basis (Fin 3) F K) :
    (correctedFinalComputeAllGates n b).length = 418 := by
  have hrest :
      (finalBaseTransitionGates (F := F) n ++ correctedCore b ++ correctedAux b ++
        correctedCompileList b correctedEndpoint2 ++
        correctedCompileList b correctedEndpoint4 ++
        finalEndpointEqualityChecks).length = 313 := by
    simp [correctedCore, correctedAux, corrected_lowered_counts, finalEndpointEqualityChecks]
  simp only [correctedFinalComputeAllGates, List.length_append] at hrest ⊢
  rw [hrest, formRCertificateGates_length, correctedCompileList_length]
  rfl

theorem correctedFinalComputeAllGates_degree
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (n : ℕ) (b : Basis (Fin 3) F K) :
    ∀ g ∈ correctedFinalComputeAllGates n b, g.degree ≤ 4 := by
  intro g hg
  simp only [correctedFinalComputeAllGates, List.mem_append] at hg
  rcases hg with (((((((hb | hc) | ha) | h2) | h4) | heq) | hcert) | hlam) | hexp
  · exact (finalBaseTransitionGates_degree n g hb).trans (by decide)
  · rw [correctedCore] at hc
    obtain ⟨xs, hxs, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hxs
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hc
    exact correctedCoreCoord_degree b i k
  · rw [correctedAux] at ha
    obtain ⟨xs, hxs, ha⟩ := List.mem_flatten.mp ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hxs
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
    exact correctedAuxCoord_degree b j k
  · exact (correctedCompileList_degree b correctedEndpoint2 2
      corrected_lowered_degrees.2.1 g h2).trans (by decide)
  · exact correctedCompileList_degree b correctedEndpoint4 4
      corrected_lowered_degrees.2.2 g h4
  · exact (finalEndpointEqualityChecks_degree g heq).trans (by decide)
  · exact formRCertificateGates_degree g hcert
  · exact correctedCompileList_degree b formRLamPins 4 formRLamPins_degree g hlam
  · exact (computeExpGates_degree g hexp).trans (by decide)

def CorrectedFinalComputeRAP
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) : RAP F :=
  { e := 3
    k := 2
    wRAP := ![297, 6]
    w := 303
    w_eq := by simp [Fin.sum_univ_two]
    h := h
    d := 4
    s := (correctedFinalComputeAllGates n b).length
    ω := orbit.ω
    β := orbit.βcoset
    I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
    C := fun i => coeffToMv chalVal pubVal ((correctedFinalComputeAllGates n b).get i)
    C_vars := fun _i => coeffToMv_vars chalVal pubVal _
    C_deg := fun _i => (coeffToMv_totalDegree_le chalVal pubVal _).trans
      (correctedFinalComputeAllGates_degree n b _ (List.get_mem _ _))
    H := H
    β_ne_zero := orbit.βcoset_ne_zero
    I_bound := by
      intro q hq
      have hq2 : q.2 = 0 ∨ q.2 = 1 := by
        have h2 := (Finset.mem_product.mp hq).2
        simpa [Finset.mem_insert, Finset.mem_singleton] using h2
      have hge : 2 ≤ 2 ^ h := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) orbit.h_pos
      rcases hq2 with hq' | hq' <;> rw [hq'] <;> omega }

def CorrectedFinalFixedPreprocessingRAP
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) : FixedPreprocessingRAP F where
  rap := CorrectedFinalComputeRAP (n := n) b chalVal pubVal orbit (rowNodeSet nodes)
  rounds_pos := by norm_num [CorrectedFinalComputeRAP]
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨11 + (j : ℕ), by
          change 11 + (j : ℕ) < 297
          omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

abbrev CorrectedNamedComputeRAP := @CorrectedFinalFixedPreprocessingRAP

abbrev ProductionFinalComputeRAP := @CorrectedFinalComputeRAP

abbrev ProductionNamedComputeRAP := @CorrectedFinalFixedPreprocessingRAP

def CorrectedFinalComputeCompiledLanguage
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).rap.w → F[X]) : Prop :=
  (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).BindsPreprocessing P ∧
    ∀ x ∈ rowNodeSet nodes, ∀ g ∈ correctedFinalComputeAllGates n b,
      g.eval (envOfTrace P orbit.ω x chalVal pubVal) = 0

theorem productionNamedComputeRAP_satisfies_iff_compiledLanguage
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing
        (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit) P ↔
      CorrectedFinalComputeCompiledLanguage hn nodes b chalVal pubVal orbit P := by
  let R := ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit
  have key : ∀ (i : Fin R.rap.s) (x : F),
      (R.rap.compose P i).eval x =
        ((correctedFinalComputeAllGates n b).get i).eval
          (envOfTrace P orbit.ω x chalVal pubVal) := by
    intro i x
    rw [Reify.compose_eval]
    exact eval_coeffToMv P orbit.ω x chalVal pubVal _
  constructor
  · rintro ⟨hraw, hfixed⟩
    refine ⟨hfixed, ?_⟩
    intro x hx g hg
    obtain ⟨i, hget⟩ := List.mem_iff_get.mp hg
    have hz := hraw i x hx
    rw [key i x] at hz
    rwa [← hget]
  · rintro ⟨hfixed, hall⟩
    refine ⟨?_, hfixed⟩
    intro i x hx
    rw [key i x]
    exact hall x hx _ (List.get_mem _ _)

theorem production_not_satisfies_of_gate_nonzero
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).rap.w → F[X])
    (x : F) (hx : x ∈ rowNodeSet nodes)
    (g : CoeffExpr F) (hg : g ∈ correctedFinalComputeAllGates n b)
    (hbad : g.eval (envOfTrace P orbit.ω x chalVal pubVal) ≠ 0) :
    ¬ RAP.SatisfiesWithPreprocessing
      (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit) P := by
  intro hsat
  have hall := (productionNamedComputeRAP_satisfies_iff_compiledLanguage
    hn nodes b chalVal pubVal orbit P).1 hsat
  exact hbad (hall.2 x hx g hg)

theorem production_wrong_preprocessing_rejected
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).rap.w → F[X])
    (j : Fin (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).fixedCount)
    (hwrong :
      P ((ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).preprocessingColumn j) ≠
        (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).preprocessing j) :
    ¬ RAP.SatisfiesWithPreprocessing
      (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit) P :=
  RAP.not_satisfiesWithPreprocessing_of_wrong _ _ j hwrong

theorem corrected_rap_fingerprint
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    let R := CorrectedFinalComputeRAP (n := n) b chalVal pubVal orbit H
    R.w = 303 ∧ R.s = 418 ∧ R.d = 4 ∧ R.k = 2 ∧ R.e = 3 := by
  exact ⟨rfl, correctedFinalComputeAllGates_length n b, rfl, rfl, rfl⟩

end
end OptimizedComputeCorrectedFinal
end Nock.NockVMROM.Thm54
