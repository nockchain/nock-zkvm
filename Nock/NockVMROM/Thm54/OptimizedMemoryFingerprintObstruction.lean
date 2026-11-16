import Nock.NockVMROM.Thm54.OptimizedMemoryRAP

/-!
# Fixed-mask obstruction to all-fourteen full-production discrimination

The optimized memory source fixes base columns `4` and `5` to the first/last-row Lagrange masks.
Consequently their booleanity gates (base IDs `5` and `6`) are already implied, on every committed
row node, by fixed preprocessing alone.  This is the exact obstruction to requiring every one of
all fourteen base gates to be independently load-bearing in the *complete* production acceptance
notion while retaining those same fixed masks.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedMemoryFingerprintObstruction

open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Polynomial
open Module
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K]

def FirstLastMaskBinding {n : ℕ} (nodes : Fin n → F)
    (P : Fin 182 → F[X]) : Prop :=
  P ⟨4, by omega⟩ = OptimizedMemoryCanonicalTrace.firstRowMask nodes ∧
    P ⟨5, by omega⟩ = OptimizedMemoryCanonicalTrace.lastRowMask nodes

theorem firstLastMaskBinding_of_source_binds
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (kMem : ℕ) (P : Fin 182 → F[X])
    (hbind :
      (namedSourceMemoryRAP hn nodes b chalVal pubVal orbit kMem).BindsPreprocessing P) :
    FirstLastMaskBinding nodes P := by
  constructor
  · exact hbind (0 : Fin 4)
  · exact hbind (1 : Fin 4)

def firstMaskBaseGate : CoeffExpr F := bbool (bcur 4)
def lastMaskBaseGate : CoeffExpr F := bbool (bcur 5)

def historicalBaseTransitionGates : List (CoeffExpr F) :=
  [bbool (bcur 0), bbool (bcur 1), bbool (bcur 2), bbool (bcur 3),
   bsum4 .traceCur, firstMaskBaseGate, lastMaskBaseGate,
   sampledTerminalCoord 0, sampledTerminalCoord 1, sampledTerminalCoord 2,
   sampledAccumulatorCoord 0, sampledAccumulatorCoord 1, sampledAccumulatorCoord 2,
   CoeffExpr.mul (CoeffExpr.sub (CoeffExpr.const 1) (bcur 5))
     (CoeffExpr.sub (extCoord .traceCur 28 0) (extCoord .traceNext 27 0))]

theorem firstMaskBaseGate_is_id5 :
    (historicalBaseTransitionGates (F := F)).get
      ⟨5, by simp [historicalBaseTransitionGates]⟩ =
        firstMaskBaseGate := rfl

theorem lastMaskBaseGate_is_id6 :
    (historicalBaseTransitionGates (F := F)).get
      ⟨6, by simp [historicalBaseTransitionGates]⟩ =
        lastMaskBaseGate := rfl

/-- Fixed preprocessing alone forces base gate ID `5` (first-mask booleanity) to vanish at every
committed row node. -/
theorem first_mask_base_gate_implied_by_fixed_preprocessing
    {h n : ℕ} (nodes : Fin n → F) (hnodes : Function.Injective nodes)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin 182 → F[X]) (hbind : FirstLastMaskBinding nodes P) (i : Fin n) :
    firstMaskBaseGate.eval
      (envOfTrace P orbit.ω (nodes i) chalVal pubVal) = 0 := by
  have heval := congrArg (fun q : F[X] => q.eval (nodes i)) hbind.1
  rw [OptimizedMemoryCanonicalTrace.firstRowMask_eval nodes hnodes i] at heval
  change (P ⟨4, by omega⟩).eval (nodes i) *
    ((P ⟨4, by omega⟩).eval (nodes i) - 1) = 0
  by_cases hi : (i : ℕ) = 0
  · simpa [hi] using congrArg (fun q : F => q * (q - 1)) heval
  · simpa [hi] using congrArg (fun q : F => q * (q - 1)) heval

/-- Fixed preprocessing alone likewise forces base gate ID `6` (last-mask booleanity). -/
theorem last_mask_base_gate_implied_by_fixed_preprocessing
    {h n : ℕ} (nodes : Fin n → F) (hnodes : Function.Injective nodes)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin 182 → F[X]) (hbind : FirstLastMaskBinding nodes P) (i : Fin n) :
    lastMaskBaseGate.eval
      (envOfTrace P orbit.ω (nodes i) chalVal pubVal) = 0 := by
  have heval := congrArg (fun q : F[X] => q.eval (nodes i)) hbind.2
  rw [OptimizedMemoryCanonicalTrace.lastRowMask_eval nodes hnodes i] at heval
  change (P ⟨5, by omega⟩).eval (nodes i) *
    ((P ⟨5, by omega⟩).eval (nodes i) - 1) = 0
  by_cases hi : (i : ℕ) + 1 = n
  · simpa [hi] using congrArg (fun q : F => q * (q - 1)) heval
  · simpa [hi] using congrArg (fun q : F => q * (q - 1)) heval

/-- Therefore the requested all-fourteen discrimination statement is false for the complete
fixed-preprocessing production object: ID `5` can never be nonzero at a committed row while the
preprocessing binding is retained. -/
theorem no_all_fourteen_full_production_discrimination
    {h n : ℕ} (nodes : Fin n → F) (hnodes : Function.Injective nodes)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) :
    ¬ (∀ j : Fin 14, ∃ (P : Fin 182 → F[X]) (i : Fin n),
      FirstLastMaskBinding nodes P ∧
      ((historicalBaseTransitionGates (F := F)).get
        ⟨j, by simpa [historicalBaseTransitionGates] using j.isLt⟩).eval
          (envOfTrace P orbit.ω (nodes i) chalVal pubVal) ≠ 0) := by
  intro hall
  obtain ⟨P, i, hbind, hne⟩ := hall (5 : Fin 14)
  change firstMaskBaseGate.eval
    (envOfTrace P orbit.ω (nodes i) chalVal pubVal) ≠ 0 at hne
  exact hne
    (first_mask_base_gate_implied_by_fixed_preprocessing
      nodes hnodes chalVal pubVal orbit P hbind i)

end
end OptimizedMemoryFingerprintObstruction
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryFingerprintObstruction.firstLastMaskBinding_of_source_binds
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryFingerprintObstruction.first_mask_base_gate_implied_by_fixed_preprocessing
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryFingerprintObstruction.last_mask_base_gate_implied_by_fixed_preprocessing
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryFingerprintObstruction.no_all_fourteen_full_production_discrimination
