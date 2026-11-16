/-
**`toy1_witness`**, the kernel non-vacuity certificate of `exec_e2e_J8F` (Exec/E2EJ8F.lean) at the real regenerated toy1 instance `toy1X`
(Exec/Toy1X.lean, Exec/Toy1XOk.lean) and, for the bound to bite, the false-claim twin `toy1XF` (the claim `*[0 [1 0]] = 1`).
Every non-adversary hypothesis of `exec_e2e_J8F` is instantiated: `hl hsh hshX hchips hnum0 hmask hnumeralOk hS hlink hids hjet`, the datum `D`/`hdk`
(`DX … 1 0 claim`, `datX_ok`), and `R`/`hT`/`hσ`/`hfree` = `RJ8`/`rfl`/`rfl`/`hfree_J8`.  The remaining binders (adversary, protocol instances, `encZ decZ hz`, `m0 mf`,
`I0 I Ifin`) are the adversary / protocol parameters of `exec_e2e_final` and stay universally quantified.  No existing file edited.
-/
import NockvmE2E.Exec.E2EJ8ToyD
import NockvmE2E.Exec.E2EJ8F

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.E2EJ8Toy
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J8Shape NockvmE2E.Exec.Toy1X NockvmE2E.Exec.E2EJ8ToyD
open NockvmE2E.Exec.E2EMain (XI170)
open NockvmE2E.J8.InstJ8
open NockvmE2E.J8.InstJ8W (sigmaX RJ8 hfree_J8)
open NockvmE2E.Exec.E2EJ8F (numOf)

noncomputable section

theorem hnum0 : ∀ t : Fin (XI170 toy1X).tabs.size,
    (chipNumeral (XI170 toy1X).tabs[t].chip).getD 0 = numOf Dtoy.d (sigmaX (XI170 toy1X) t) := by
  intro t; fin_cases t <;> decide +kernel

theorem hnum0F : ∀ t : Fin (XI170 toy1XF).tabs.size,
    (chipNumeral (XI170 toy1XF).tabs[t].chip).getD 0 = numOf DtoyF.d (sigmaX (XI170 toy1XF) t) := by
  intro t; fin_cases t <;> decide +kernel

/-- no table is the jet, so `hjet` (the jet's registry columns) is vacuous -/
theorem nojet : ∀ t : Fin (XI170 toy1X).tabs.size, (XI170 toy1X).tabs[t].chip.id ≠ "jetChipJ8" := by
  intro t; fin_cases t <;> decide +kernel
theorem nojetF : ∀ t : Fin (XI170 toy1XF).tabs.size, (XI170 toy1XF).tabs[t].chip.id ≠ "jetChipJ8" := by
  intro t; fin_cases t <;> decide +kernel

/-- **`toy1_witness`**: the non-adversary hypotheses of `exec_e2e_J8F` at `toy1X` (claim TRUE: `*[0 [1 0]] = 0`) -/
theorem toy1_witness :
    ∃ (hsh : j8ShapeOk (XI170 toy1X) = true) (hshX : j8ShapeXOk (XI170 toy1X) = true)
      (D : NockvmE2E.Exec.E2EJ8.J8X.DatX (XI170 toy1X) hsh) (hdk : DatumOK D.d),
      toy1X.l = 170 ∧ chipsOk (XI170 toy1X) = true ∧
      (∀ t : Fin (XI170 toy1X).tabs.size,
        (chipNumeral (XI170 toy1X).tabs[t].chip).getD 0 = numOf D.d (sigmaX (XI170 toy1X) t)) ∧
      StmtP D.d ∧ NockvmE2E.J8.RVUJ8.InpLink D.d (XI170 toy1X).pubIn ∧ (∀ id ∈ D.d.Pb.regs, id < P) ∧
      MaskOk.maskOk (XI170 toy1X) = true ∧ MaskOk.numeralOk (XI170 toy1X) = true ∧
      (∀ t : Fin (XI170 toy1X).tabs.size, (XI170 toy1X).tabs[t].chip.id ≠ "jetChipJ8") ∧
      D.d.c = NockvmE2E.J8.RVUJ8.toyClaim ∧ Nock.Jet.HoldsN D.d.c :=
  ⟨hsh, hshX, Dtoy, dat_toy.1, rfl, hchips, hnum0, dat_toy.2, hlink, hids, hmask, hnumeralOk, nojet, rfl, ⟨1, by decide⟩⟩

/-- **the false-claim twin**: the same hypotheses hold at `toy1XF` and `¬ HoldsN` the claim, so the event `AccF ∧ ¬ HoldsN` of the bound is not empty -/
theorem toy1_witness_false :
    ∃ (hsh : j8ShapeOk (XI170 toy1XF) = true) (hshX : j8ShapeXOk (XI170 toy1XF) = true)
      (D : NockvmE2E.Exec.E2EJ8.J8X.DatX (XI170 toy1XF) hsh) (hdk : DatumOK D.d),
      toy1XF.l = 170 ∧ chipsOk (XI170 toy1XF) = true ∧
      (∀ t : Fin (XI170 toy1XF).tabs.size,
        (chipNumeral (XI170 toy1XF).tabs[t].chip).getD 0 = numOf D.d (sigmaX (XI170 toy1XF) t)) ∧
      StmtP D.d ∧ NockvmE2E.J8.RVUJ8.InpLink D.d (XI170 toy1XF).pubIn ∧ (∀ id ∈ D.d.Pb.regs, id < P) ∧
      MaskOk.maskOk (XI170 toy1XF) = true ∧ MaskOk.numeralOk (XI170 toy1XF) = true ∧
      (∀ t : Fin (XI170 toy1XF).tabs.size, (XI170 toy1XF).tabs[t].chip.id ≠ "jetChipJ8") ∧
      ¬ Nock.Jet.HoldsN D.d.c :=
  ⟨hshF, hshXF, DtoyF, dat_toyF.1, rfl, hchipsF, hnum0F, dat_toyF.2, hlinkF, hidsF, hmaskF, hnumeralOkF, nojetF, not_holds_F⟩

end

end NockvmE2E.Exec.E2EJ8Toy

#print axioms NockvmE2E.Exec.E2EJ8Toy.toy1_witness
#print axioms NockvmE2E.Exec.E2EJ8Toy.toy1_witness_false
