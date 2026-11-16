import Nock.RedTeam.Batch1173Thm54C2CombinedServedRecords
import Nock.RedTeam.Batch1142Thm54C2CombinedCertAxes0
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1175Thm54PositionalNoWeaker.lean

  R1: `Batch1171.RecOK` is `Batch1110.RecOK` (`rfl`).  R2 (`pr_inTree`): a positional pair is a
  reached pair.  R3 (`servedRecordsOK_imp_pos`): `Batch1111.ServedRecordsOK → Batch1172.ServedRecordsPos`
  at every package/coin/trace, so `Batch1173` is no weaker than `Batch1142`.
-/

namespace Nock.RedTeam.Batch1175
open Nock Nock.Walk Nock.RedTeam

open Nock Nock.Walk Nock.RedTeam

/-- R1: the oracle body is unchanged (Batch1171.RecOK is Batch1110.RecOK). -/
example : @Batch1171.RecOK = @Batch1110.RecOK := rfl

/-- R2: a positional pair is a reached pair (PR ⊆ InTree × InTree). -/
theorem pr_inTree {α β : Type} {t u : NTree α} {T w : NTree β} (h : Batch1171.PR t T u w) :
    InTree t u ∧ InTree T w := by
  induction h with
  | root => exact ⟨InTree.here _, InTree.here _⟩
  | @child u0 w0 uc wc i _ hu hw ih =>
    exact ⟨InTree_trans ih.1 (InTree.sub (List.mem_of_getElem? hu) (InTree.here _)),
           InTree_trans ih.2 (InTree.sub (List.mem_of_getElem? hw) (InTree.here _))⟩
#print axioms pr_inTree

theorem servedRecordsOK_imp_pos {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [DecidableEq F]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K] {hOrb : ℕ}
    (P : Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)
    (c : Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → Polynomial F) (Qm : Fin (P.memoryChipAt c).rap.w → Polynomial F)
    (h : Batch1111.ServedRecordsOK P c Qc Qm) : Batch1172.ServedRecordsPos P c Qc Qm := by
  intro u s f hpr
  have ⟨h1, h2⟩ := pr_inTree hpr
  exact h u s f h1 h2
#print axioms servedRecordsOK_imp_pos

end Nock.RedTeam.Batch1175
