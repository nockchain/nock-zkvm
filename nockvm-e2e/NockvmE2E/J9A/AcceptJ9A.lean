/-
  NockvmE2E/J9A/AcceptJ9A.lean   (non-vacuity of the public check)

  P0 showed that at `pubMode = 0` the public check of any instance with `layOkF famJ9A` is identically false.
  Here: at `pubMode = 2` the opposite.  `accXI` is a pubMode-2 `ExecInst` whose public layout satisfies `layOkF famJ9A` (8 tables, `tabLens9`),
  and `XI.pubCheck` ACCEPTS the balanced axis/split vector `toy9On` (axOn = spOn = true) at `toy1Slots`.  The same layout is REJECTED by the
  J-8 check `PE.pubCheck` (the P0 negation).
  NOT shown here: a `verifyFlat` ACCEPT of a full J-9 A proof (needs a J-9 A trace, nockvm V1J9A).
-/
import NockvmE2E.Exec.J9AChipsFam
import NockvmE2E.Exec.Flat
import NockvmE2E.Exec.PubExe9
set_option autoImplicit false

namespace NockvmE2E.J9A.AcceptJ9A
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips

/-- table index -> chip id (the order of `tabOf9`) -/
def tabIds : Array String :=
  #["computeChipVCLHX9", "cellChipHQKW", "walkChipJ8", "jetChipJ8", "atomChipHQL", "walkChipHQK", "axisChipJ9", "splitChipJ9"]

def dummyChip (id : String) : Tr.Chip := ⟨id, #[], #[], #[], #[], #[], 0, 0⟩

def tabAt (i : Nat) : TabInst :=
  ⟨1, 0, PE.tabLens9[i]!, PE.tabLens9[i]!, (PE.layoutOf9 PE.toy9On).bases[i]!, dummyChip tabIds[i]!⟩

/-- a pubMode-2 instance with the eight J-9 A tables and the `toy9On` public layout -/
def accXI : ExecInst :=
  { nD := 5, dShift := 7, dGen := 2, hN := 1, hGen := 1, hShift := 1, r := 2, k := 1, d := 1, l := 4, nc := 0, nq := 0,
    colKind := #[], blockOf := #[], pre := #[], pubOf := #[], ppt := VF.K3.one, nCoins := #[0, 0], derived := #[],
    tabs := (List.range 8).toArray.map tabAt, pubIn := PE.toy1Claim, pubLay := PE.layoutOf9 PE.toy9On, slotOf := PE.idSlots,
    pubMode := 2 }

theorem accXI_mode : accXI.pubMode = famJ9A.pubMode := rfl

theorem accXI_layOk : layOkF famJ9A accXI = true := by decide +kernel

theorem accXI_accepts : accXI.pubCheck PE.toy1Slots (PE.concatPubs PE.toy9On) = true := by decide +kernel

/-- the J-8 check rejects the same data (P0: its `okShape` needs six tables) -/
theorem accXI_J8_rejects : PE.pubCheck accXI.pubIn accXI.pubLay accXI.slotOf PE.toy1Slots (PE.concatPubs PE.toy9On) = false := by
  decide +kernel

/-- **acceptance (non-vacuity of `exec_e2e_J9A_absent`'s public check)**: a pubMode-2 instance with `layOkF famJ9A` whose
`ExecInst.pubCheck` is NOT identically false (it accepts `toy9On` at `toy1Slots`). -/
theorem pubCheck_J9A_not_vacuous :
    ∃ XI : ExecInst, XI.pubMode = famJ9A.pubMode ∧ layOkF famJ9A XI = true ∧
      ∃ (slots : Array VF.K3) (pub : Array VF.G), XI.pubCheck slots pub = true :=
  ⟨accXI, accXI_mode, accXI_layOk, _, _, accXI_accepts⟩

end NockvmE2E.J9A.AcceptJ9A
#print axioms NockvmE2E.J9A.AcceptJ9A.pubCheck_J9A_not_vacuous
#print axioms NockvmE2E.J9A.AcceptJ9A.accXI_J8_rejects
