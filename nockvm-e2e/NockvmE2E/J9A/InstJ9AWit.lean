/-
vacuity: `StmtP9A ∧ PubP9A` are inhabited at the chips-ABSENT record of nock's
`Batch4882.complJ9A_absent_toy` (`*[(p+5) [0 1]]`, empty registry, `axOn = spOn = false`), via `stmt_pub_of_acc9`.
`DatumOK9A` at that record is NOT proved here: see the end of the file.
-/
import NockvmE2E.J9A.InstJ9A
import Nock.RedTeam.Batch4882Thm54J9AComplAbsent

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.J9A.InstJ9AWit

open NockvmE2E.J9A.InstJ9A
open NockvmE2E.J8.InstJ8 (P Φ0)
open Nock.RedTeam.Batch4856 (B9T s9)
open Nock.RedTeam.Batch4882
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAbsent (pubA msgA trA rowsA)
open Nock.TraceGenExe

noncomputable section

/-- the datum of the chips-absent toy record: `pubA B9T.Pb` (both new chips absent, one dummy row each), the empty registry,
the toy claim, nock's own rows `rowsA B9T.rows`, `g = B9T.g` (the union-domain fields `hN = 1`, `ω = 1` are dummies; they enter
`DatumOK9A` only, not `StmtP9A` / `PubP9A`) -/
def dT : Datum9A :=
  ⟨pubA B9T.Pb, Nock.Jet.VerifiedRegistry.empty.R, Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8.cJ s9
    Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base.f0 s9, rowsA B9T.rows, B9T.g, 1, 1⟩

/-- **`StmtP9A` and `PubP9A` are inhabited at the chips-absent record**: the J-9 A analogue of `InstJ8.stmt_pub_inhabited`, from
nock's accepting coin of `complJ9A_absent_toy_figure` and `stmt_pub_of_acc9`. -/
theorem stmt_pub_inhabited9 : ∃ (χ : Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC) (M : Msg9), StmtP9A dT ∧ PubP9A dT χ M := by
  obtain ⟨-, χ, hχ⟩ := complJ9A_absent_toy_figure
  exact ⟨χ, _, (stmt_pub_of_acc9 dT χ _ _ hχ).1, (stmt_pub_of_acc9 dT χ _ _ hχ).2⟩

/-- both new chips are absent at this record (so `present9A dT` excludes exactly the jet / atom walk / axis / split tables) -/
theorem dT_absent : dT.Pb.axOn = false ∧ dT.Pb.spOn = false := ⟨rfl, rfl⟩

end

end NockvmE2E.J9A.InstJ9AWit

#print axioms NockvmE2E.J9A.InstJ9AWit.stmt_pub_inhabited9
