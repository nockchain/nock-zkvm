/-
  NockvmE2E/Emit/Compute.lean   (c)

  **The compute chip's 54 accumulator gates as 18 `𝕂`-valued gates.**  In `ChipHX.baseGatesHX` the three LogUp
  accumulators over `𝕂′` (six `𝕂`-columns: export / path / service, Re and Im) are written COORDINATE-WISE: for each
  accumulator `A` (a round-1 `𝕂`-column at physical `accBase .. accBase+2`) the base gates
  `isFirst · A_k`, `(1 − isLast)(A′_k − A_k − t_k)`, `isLast (A_k + t_k − pub_k)` for `k < 3`, where
  `t_k = Σ_s act_s · inv_s,k` (`LogUpAcc.termCoord`) reads the round-1 `𝕂`-columns `inv_s` and the round-0 base activities
  `act_s`.  They are `𝕂`-linear with base coefficients, i.e. the three coordinates of ONE `𝕂`-valued gate each.  A coordinate
  of a round-1 `𝕂` column is not a base-field quantity, so they belong at ROUND 1 as `𝕂`-gates.

  `accKGatesHX` states them as `MixedExpr`s (at the `col0Id` leaf convention of `gatesHX`), and
  `accGatesHX_semK` proves, for any field `F`, any extension `K` with basis `b` and every environment, that the coordinate
  expansion `mixedCompile b col0Id` of `accKGatesHX` evaluates, gate by gate and in order, exactly as `accGatesHX`.
  (Syntactic equality does not hold only because the sum's tail is `.const 0` vs `Const 0`.)  `accGatesHX_cast` shows the
  `ℚ → 𝔽_p` cast of `accGatesHX` (what `baseGatesFX` uses) is `accGatesHX` at `𝔽_p`.
-/
import NockvmE2E.Emit.Dag
import Nock.NockVMROM.Thm54.VclL.Handle.ChipHX

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.Emit

open Nock.Reified Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Module Nock.NockVMROM.Thm54.VclL.Handle.ChipH Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD

section KGates
variable {F : Type} [Field F]

/-- `t = Σ_s act_s · inv_s` as a `𝕂` expression (tail `Const 0`). -/
def termK (slots : List (Slot F)) : MixedExpr F :=
  slots.foldr (fun s acc => .Add (.Scale s.act (.Var .traceCur s.invBase)) acc) (.Const 0)

/-- The three `𝕂` gates (init, step, terminal) of one accumulator, the 3-coordinate expansion of `accGatesX`. -/
def accKGates (slots : List (Slot F)) (accBase pubBase : ℕ) : List (MixedExpr F) :=
  [ .Scale (cc firstX) (.Var .traceCur accBase),
    .Scale (notC lastX) (.Sub (.Sub (.Var .traceNext accBase) (.Var .traceCur accBase)) (termK slots)),
    .Scale (cc lastX) (.Sub (.Add (.Var .traceCur accBase) (termK slots)) (.Var .publicVal pubBase)) ]

def accKOf (b : Bal) (im : Bool) (accBase pubBase : ℕ) : List (MixedExpr F) :=
  accKGates (slotsX.map fun S => ⟨S.actB b, if im then S.invIm else S.inv⟩) accBase pubBase

/-- The 18 `𝕂`-valued accumulator gates (same order as `accGatesHX`'s six blocks). -/
def accKGatesHX : List (MixedExpr F) :=
  accKOf .x false accXX pubRhoX ++ accKOf .x true accXXi pubRhoXIm ++
  accKOf .p false accPX pubRhoP ++ accKOf .p true accPXi pubRhoPIm ++
  accKOf .s false accSX pubRhoSX ++ accKOf .s true accSXi pubRhoSXi

end KGates

section Sem
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem eval_termK_coord (b : Basis (Fin 3) F K) (slots : List (Slot F)) (k : Fin 3) (env : Env F) :
    ((mixedCompile b col0Id (termK slots)) k).eval env = (termCoord slots k).eval env := by
  induction slots with
  | nil => simp [termK, termCoord, CoeffExpr.sumList, mixedCompile, CoeffExpr.eval]
  | cons s l ih =>
    simp only [termK, termCoord, CoeffExpr.sumList, List.foldr_cons] at ih ⊢
    simp [mixedCompile, CoeffExpr.eval, ih, col0Id]

theorem accGatesX_semK (b : Basis (Fin 3) F K) (slots : List (Slot F)) (accBase pubBase : ℕ) (env : Env F) :
    ((accGatesX slots accBase pubBase).map (·.eval env)) =
      (((accKGates slots accBase pubBase).flatMap fun g => List.ofFn (mixedCompile b col0Id g)).map (·.eval env)) := by
  have h0 := eval_termK_coord b slots 0 env
  have h1 := eval_termK_coord b slots 1 env
  have h2 := eval_termK_coord b slots 2 env
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  simp [accGatesX, accKGates, accInitX, accStepX, accTermX, List.range_succ, List.ofFn_succ, mixedCompile,
    CoeffExpr.eval, col0Id, cc, h0, h1, h2]

/-- **The 54 coordinate-level accumulator gates of `baseGatesHX` are the coordinate expansion of the 18 `𝕂` gates
`accKGatesHX`** (evaluation, gate by gate and in order, for every environment and every basis). -/
theorem accGatesHX_semK (b : Basis (Fin 3) F K) (env : Env F) :
    ((accGatesHX (F := F)).map (·.eval env)) =
      (((accKGatesHX (F := F)).flatMap fun g => List.ofFn (mixedCompile b col0Id g)).map (·.eval env)) := by
  simp only [accGatesHX, accKGatesHX, accOf, accKOf, List.flatMap_append, List.map_append,
    accGatesX_semK b _ _ _ env]

end Sem

theorem accGatesHX_length : (accGatesHX (F := ℚ)).length = 54 := by decide +kernel

/-- `accGatesHX` at `𝔽_p` is the cast of `accGatesHX` at `ℚ` (the form `baseGatesFX` uses). -/
theorem accGatesHX_cast :
    (accGatesHX (F := Gl)) = (accGatesHX (F := ℚ)).map (mapC (fun q : ℚ => (q : Gl))) := by
  decide +kernel


end Nock.Emit

#print axioms Nock.Emit.accGatesHX_semK
#print axioms Nock.Emit.accGatesHX_cast
#print axioms Nock.Emit.accGatesHX_length
