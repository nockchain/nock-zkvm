/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestCongH.lean

  Additive.

  * §1 `rdsQ` / `rdsK` / `rdsF`: the variables a `ℚ`-template gate reads (as `(kind, index)` pairs), and
    `evalQ_congr_rds` / `evalMQ_congr_rds`: two environments that agree on the read set evaluate a gate equally.
  * §2 the read sets of the compute chip's gates, by `decide`: the 𝕂 side of the nine walk gates reads
    only `wLn / wCnt / wAcc / wInv`, the walk coins and the publics `pubIC / pubSeed / pubOut`; the base side only
    columns `< 43`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestAttainH
import Nock.NockVMROM.Thm54.VclL.Handle.WalkGatesH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun Nock.Walk Nock.Reified Module
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC
open Nock.NockVMROM.Thm54.VclL.Handle.IOVS

noncomputable section

section Cong

/-- The value an environment gives to a variable. -/
def envRd {F : Type} (e : Env F) : VarKind × ℕ → F
  | (.traceCur, i) => e.trace i
  | (.traceNext, i) => e.traceNext i
  | (.challenge, i) => e.chal i
  | (.publicVal, i) => e.pub i

/-- The variables a `ℚ`-template base expression reads. -/
def rdsQ : CoeffExpr ℚ → List (VarKind × ℕ)
  | .const _ => []
  | .var k i => [(k, i)]
  | .add a b => rdsQ a ++ rdsQ b
  | .sub a b => rdsQ a ++ rdsQ b
  | .mul a b => rdsQ a ++ rdsQ b
  | .neg a => rdsQ a
  | .pow a _ => rdsQ a

/-- The `𝕂`-leaf variables a mixed expression reads (the `Var` leaves). -/
def rdsK : MixedExpr ℚ → List (VarKind × ℕ)
  | .Var k i => [(k, i)]
  | .Lift _ => []
  | .Scale _ u => rdsK u
  | .Const _ => []
  | .Add a b => rdsK a ++ rdsK b
  | .Sub a b => rdsK a ++ rdsK b
  | .Neg a => rdsK a
  | .Mul a b => rdsK a ++ rdsK b
  | .Pow a _ => rdsK a

/-- The base-field variables a mixed expression reads (coefficients of `Lift` / `Scale`). -/
def rdsF : MixedExpr ℚ → List (VarKind × ℕ)
  | .Var _ _ => []
  | .Lift g => rdsQ g
  | .Scale g u => rdsQ g ++ rdsF u
  | .Const _ => []
  | .Add a b => rdsF a ++ rdsF b
  | .Sub a b => rdsF a ++ rdsF b
  | .Neg a => rdsF a
  | .Mul a b => rdsF a ++ rdsF b
  | .Pow a _ => rdsF a

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem evalQ_congr_rds (g : CoeffExpr ℚ) (e1 e2 : Env F) (h : ∀ p ∈ rdsQ g, envRd e1 p = envRd e2 p) :
    evalQ g e1 = evalQ g e2 := by
  induction g with
  | const c => rfl
  | var k i => have := h (k, i) (by simp [rdsQ]); cases k <;> exact this
  | add a b iha ihb =>
    simp only [rdsQ, List.mem_append] at h
    simp only [evalQ, iha (fun p hp => h p (Or.inl hp)), ihb (fun p hp => h p (Or.inr hp))]
  | sub a b iha ihb =>
    simp only [rdsQ, List.mem_append] at h
    simp only [evalQ, iha (fun p hp => h p (Or.inl hp)), ihb (fun p hp => h p (Or.inr hp))]
  | mul a b iha ihb =>
    simp only [rdsQ, List.mem_append] at h
    simp only [evalQ, iha (fun p hp => h p (Or.inl hp)), ihb (fun p hp => h p (Or.inr hp))]
  | neg a ih => simp only [evalQ, ih (fun p hp => h p (by simpa [rdsQ] using hp))]
  | pow a n ih => simp only [evalQ, ih (fun p hp => h p (by simpa [rdsQ] using hp))]

theorem evalMQ_congr_rds (g : MixedExpr ℚ) (eK1 eK2 : Env K) (eF1 eF2 : Env F)
    (hK : ∀ p ∈ rdsK g, envRd eK1 p = envRd eK2 p) (hF : ∀ p ∈ rdsF g, envRd eF1 p = envRd eF2 p) :
    evalMQ g eK1 eF1 = evalMQ g eK2 eF2 := by
  induction g with
  | Var k i => have := hK (k, i) (by simp [rdsK]); cases k <;> exact this
  | Lift g => simp only [evalMQ, evalQ_congr_rds g eF1 eF2 (by simpa [rdsF] using hF)]
  | Scale g u ih =>
    simp only [rdsF, List.mem_append] at hF
    simp only [evalMQ, evalQ_congr_rds g eF1 eF2 (fun p hp => hF p (Or.inl hp)),
      ih (by simpa [rdsK] using hK) (fun p hp => hF p (Or.inr hp))]
  | Const c => rfl
  | Add a b iha ihb =>
    simp only [rdsK, rdsF, List.mem_append] at hK hF
    simp only [evalMQ, iha (fun p hp => hK p (Or.inl hp)) (fun p hp => hF p (Or.inl hp)),
      ihb (fun p hp => hK p (Or.inr hp)) (fun p hp => hF p (Or.inr hp))]
  | Sub a b iha ihb =>
    simp only [rdsK, rdsF, List.mem_append] at hK hF
    simp only [evalMQ, iha (fun p hp => hK p (Or.inl hp)) (fun p hp => hF p (Or.inl hp)),
      ihb (fun p hp => hK p (Or.inr hp)) (fun p hp => hF p (Or.inr hp))]
  | Neg a ih => simp only [evalMQ, ih (by simpa [rdsK] using hK) (by simpa [rdsF] using hF)]
  | Mul a b iha ihb =>
    simp only [rdsK, rdsF, List.mem_append] at hK hF
    simp only [evalMQ, iha (fun p hp => hK p (Or.inl hp)) (fun p hp => hF p (Or.inl hp)),
      ihb (fun p hp => hK p (Or.inr hp)) (fun p hp => hF p (Or.inr hp))]
  | Pow a n ih => simp only [evalMQ, ih (by simpa [rdsK] using hK) (by simpa [rdsF] using hF)]

end Cong

section Reads

/-- Walk-gate 𝕂 reads. -/
def wkOK : VarKind × ℕ → Bool
  | (.traceCur, i) => i == wLn || i == wCnt || i == wAcc || i == wInv
  | (.traceNext, i) => i == wLn || i == wCnt || i == wAcc
  | (.challenge, i) => i == chalAlphaW || i == chalGammaW
  | (.publicVal, i) => i == pubIC || i == pubSeed || i == pubOut

/-- Base-side reads of the walk gates: current / next columns `< 43`. -/
def wfOK : VarKind × ℕ → Bool
  | (.traceCur, i) => decide (i < 43)
  | (.traceNext, i) => decide (i < 43)
  | _ => false

theorem walk_readsK : ∀ g ∈ (walkGates : List (MixedExpr ℚ)), ∀ p ∈ rdsK g, wkOK p = true := by decide
theorem walk_readsF : ∀ g ∈ (walkGates : List (MixedExpr ℚ)), ∀ p ∈ rdsF g, wfOK p = true := by decide

/-- The walk gates that read the next row are scaled by `1 - isLast`; the others read only current columns. -/
def noNextB : VarKind × ℕ → Bool
  | (.traceNext, _) => false
  | _ => true

def isScaleNL : MixedExpr ℚ → Bool
  | .Scale (.sub (.const c) (.var .traceCur i)) _ => (c == 1) && (i == 12)
  | _ => false

theorem walk_gate_shapeB : ∀ g ∈ (walkGates : List (MixedExpr ℚ)),
    ((∀ p ∈ rdsK g, noNextB p = true) ∧ (∀ p ∈ rdsF g, noNextB p = true)) ∨ isScaleNL g = true := by decide

theorem isScaleNL_eq (g : MixedExpr ℚ) (h : isScaleNL g = true) : ∃ u, g = MixedExpr.Scale (notLast (F := ℚ)) u := by
  match g, h with
  | .Scale (.sub (.const c) (.var .traceCur i)) u, h =>
    simp only [isScaleNL, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨u, rfl⟩

/-- Base gates read only current columns `< 43` and publics `< 6`. -/
def bsOK : VarKind × ℕ → Bool
  | (.traceCur, i) => decide (i < 43)
  | (.publicVal, i) => decide (i < 6)
  | _ => false

theorem arith_reads : ∀ g ∈ (arithGates : List (CoeffExpr ℚ)) ++ (eqGates : List (EqG ℚ)).map EqG.gate,
    ∀ p ∈ rdsQ g, bsOK p = true := by decide

end Reads

end

end Nock.NockVMROM.Thm54.VclL.Handle
