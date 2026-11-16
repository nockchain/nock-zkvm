/-
  Nock/RedTeam/Batch1796Thm54VclLZeroWeightInv.lean

  Production: `Thm54/VclL/Chips/ChipRAP.lean`
  (`Cell.qEqs` `+ (1 − wL)·consLInv`, `(1 − wR)·consRInv`; cell `s 237 → 249`, `d = 4`).

  NC pair: `Batch1795.consumer_gate_free_inv` — at the old gate list a zero-weight child whose key
  hits the pole leaves its inverse free (the row is accepted with any inverse); at the new list
  (`zero_weight_inv_rejected`) the same row with a nonzero inverse fails the new gate.
-/
import Nock.RedTeam.Batch1795Thm54VclLPathModel

namespace Nock.RedTeam.Batch1796

open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

theorem zeroWeight_gate_mem {F : Type} [Field F] (δF : F) :
    QE.scale (notE (cv Cell.wL)) (QE.var Cell.consLInv) ∈ Cell.qEqs δF ∧
      QE.scale (notE (cv Cell.wR)) (QE.var Cell.consRInv) ∈ Cell.qEqs δF := by
  constructor <;> simp [Cell.qEqs]

/-- **Rejected at the new chip**: a zero-weight left child with a nonzero inverse fails the new gate
(whatever its key's denominator). -/
theorem zero_weight_inv_rejected {F K : Type} [Field F] [Field K] [Algebra F K] (δF : F)
    (eK : Env K) (eF : Env F) (hw : eF.trace Cell.wL = 0)
    (hinv : (QE.var Cell.consLInv : QE F).ev δF eK eF ≠ 0) :
    (QE.scale (notE (cv Cell.wL)) (QE.var Cell.consLInv) : QE F).ev δF eK eF ≠ 0 := by
  rw [ev_scale]
  simpa [CoeffExpr.eval, hw, liftQ] using hinv

theorem cell_s_d {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] (δF : F)
    (b : Module.Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (orbit : Nock.NockVMROM.Thm54.StrictExtension.StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    (cellChip δF b hn nodes orbit chals pubs).rap.s = 255 ∧
      (cellChip δF b hn nodes orbit chals pubs).rap.d = 4 :=
  ⟨(cellChip_fingerprint δF b hn nodes orbit chals pubs).2.1,
    (cellChip_fingerprint δF b hn nodes orbit chals pubs).2.2.1⟩

#print axioms zeroWeight_gate_mem
#print axioms zero_weight_inv_rejected
#print axioms cell_s_d
#print axioms cellChip_deg

end Nock.RedTeam.Batch1796
