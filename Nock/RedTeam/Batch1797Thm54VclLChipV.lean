/-
  Nock/RedTeam/Batch1797Thm54VclLChipV.lean

  Production:
  `Thm54/VclL/Chips/ChipV.lean` (`okGates`, `cellChipOk` / `pathChipOk`, `GoodM`, `okOf`).

  * `cellChipOk_sat` / `pathChipOk_sat`: an accepted `ok`-gated trace has `ok = true` and satisfies
    the plain chip, so the whole bridge (`RowModel`, `PathModel`) applies with no premise on `V`.
  * NC: `GoodM V t` false ⇒ `okOf V t = false` ⇒ EVERY trace is rejected by both chips
    (`cell_rejects_bad_datum`, `path_rejects_bad_datum`).
  * Positive control: on a good datum the chips are the plain chips' gate lists
    (`okGates_true`).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.ChipV
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1797

open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.CoordinateCompiler
set_option autoImplicit false
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

section
variable {F : Type} [Field F] {K : Type} [Field K] [Algebra F K] {hC : ℕ} {S : MemShape}

theorem okOf_false {V : VerifierData F K hC S} {t : Fin S.k} (h : ¬ GoodM V t) :
    okOf V t = false := by
  cases hok : okOf V t
  · rfl
  · exact absurd (goodM_of_ok hok) h

theorem okGates_true : (okGates true : List (CoeffExpr F)) = [] := rfl

variable [FiniteDimensional F K] (δF : F) (b : Module.Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- **NC: a bad datum rejects every cell trace.** -/
theorem cell_rejects_bad_datum {V : VerifierData F K hC S} {t : Fin S.k} (hbad : ¬ GoodM V t)
    (Q : Fin (cellChipOk δF b hn nodes orbit chals pubs (okOf V t)).rap.w → Polynomial F) :
    ¬ RAP.SatisfiesWithPreprocessing (cellChipOk δF b hn nodes orbit chals pubs (okOf V t)) Q := by
  intro hQ
  have := (cellChipOk_sat δF b hn nodes orbit chals pubs (okOf V t) Q hQ).1
  rw [okOf_false hbad] at this
  exact Bool.false_ne_true this

/-- **NC: a bad datum rejects every path trace.** -/
theorem path_rejects_bad_datum {V : VerifierData F K hC S} {t : Fin S.k} (hbad : ¬ GoodM V t)
    (Q : Fin (pathChipOk δF b hn nodes orbit chals pubs (okOf V t)).rap.w → Polynomial F) :
    ¬ RAP.SatisfiesWithPreprocessing (pathChipOk δF b hn nodes orbit chals pubs (okOf V t)) Q := by
  intro hQ
  have := (pathChipOk_sat δF b hn nodes orbit chals pubs (okOf V t) Q hQ).1
  rw [okOf_false hbad] at this
  exact Bool.false_ne_true this

end

#print axioms cellChipOk_sat
#print axioms pathChipOk_sat
#print axioms goodM_of_ok
#print axioms ok_of_goodM
#print axioms cell_rejects_bad_datum
#print axioms path_rejects_bad_datum

end Nock.RedTeam.Batch1797
