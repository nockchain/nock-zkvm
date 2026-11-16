/-
  **The preg preprocessing is the verifier's `pregCol`.**  A separate module (it cannot live in `AluSatPreg`: it
  composes `AluSatPreg.preLOf_eval` with `GenPortJ9ALHAluE.col_pregCol`, whose module imports `AluSatPreg`).

  `preL_eval_pregCol`: the honest preprocessing `preLOf` of the primitive table, evaluated at row node `i`, is the
  verifier's `CheckJ9AL.pregCol ps k i`, under `col_pregCol`'s hypotheses.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAluE

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAluE

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestTable
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAlu
open Nock.Jet.Prim (PrimOp)
open Polynomial

noncomputable section

variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]

/-- **`preLOf` at a row node is the verifier's `pregCol`.**  For injective row nodes, a primitive table `ps` without
`dec`, and an honest table `tblP` of at most `n` rows, the `k`-th preprocessing polynomial `preLOf` evaluated at the
node of row `i` equals `CheckJ9AL.pregCol ps k i`. -/
theorem preL_eval_pregCol {n : ℕ} (nodes : Fin n → ZMod p) (hinj : Function.Injective nodes) (y : KQ)
    (ps : List (ℕ × PrimOp)) (vcOf mOf : ℕ → ℕ) (cls : List CallL) (hnoDec : ∀ q ∈ ps, q.2 ≠ .dec)
    (hlen : (tblP (K := KC) deltaF p y (AluSatPreg.pregsP ps vcOf mOf) cls).length ≤ n) (k : Fin 3) (i : Fin n) :
    (AluSatPreg.preLOf deltaF nodes (tblP (K := KC) deltaF p y (AluSatPreg.pregsP ps vcOf mOf) cls) k).eval (nodes i) =
      Nock.V1J9AL.CheckJ9AL.pregCol ps (k : ℕ) (i : ℕ) := by
  rw [AluSatPreg.preLOf_eval deltaF nodes hinj _ k i]
  exact col_pregCol nodes hinj y ps vcOf mOf cls hnoDec hlen k i

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAluE

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAluE
#print axioms preL_eval_pregCol
end Axioms
