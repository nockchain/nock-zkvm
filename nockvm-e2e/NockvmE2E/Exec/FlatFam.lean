/-
`loadInstF F path` (Fam wrapper over `FlatF.loadInstG`), the J-8 agreement lemma and the executed pubMode-2 acceptance witness.
Imports `ShapeF` (hence the E2E chain); `FlatF` itself does not.
-/
import NockvmE2E.Exec.FlatF
import NockvmE2E.Exec.J9AChipsFam

set_option autoImplicit false

namespace NockvmE2E.Exec.FlatFam
open Lean NockvmE2E.Exec.VF NockvmE2E.Exec.J NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.Exec.FlatF

def loadInstF (F : Fam) (path : String) : IO ExecInst := loadInstG F.ids F.tabOf F.tabLens F.pubMode path

/-- J-8 agreement: the layout builder is `layoutOfTabs` on `famJ8` (so `parseInstF famJ8` and `loadInst` differ only by the added family-id check,
which `shapeOkF`'s `mandatoryOkF` already imposes, and `pubMode := 0` = the default) -/
theorem layoutOfTabsF_famJ8 (tabs : Array TabInst) : layoutOfTabsF famJ8.tabOf famJ8.tabLens tabs = layoutOfTabs tabs := rfl
theorem pubMode_famJ8 : famJ8.pubMode = 0 := rfl
theorem pubMode_famJ9A : NockvmE2E.Exec.J9AChips.famJ9A.pubMode = 2 := rfl

/-! ## executed acceptance witness for the J-9 A public check, at the `ExecInst` level -/
def dummyChip (id : String) : Tr.Chip := ⟨id, #[], #[], #[], #[], #[], 0, 0⟩

def tab9 (F : Fam) (ps : Array (Array G)) : Array TabInst :=
  (List.range ps.size).toArray.map fun i =>
    ⟨1, 0, 0, ps[i]!.size, (PE.layoutOf ps).bases[i]!, dummyChip (F.ids.toArray.find? (fun id => F.tabOf id == some i)).get!⟩

open NockvmE2E.Exec.J9AChips in
def instOf9 (ps : Array (Array G)) : ExecInst :=
  { nD := 0, dShift := 0, dGen := 0, hN := 1, hGen := 0, hShift := 1, r := 2, k := 0, d := 1, l := 1, nc := 0, nq := 0,
    colKind := #[], blockOf := #[], pre := #[], pubOf := #[], ppt := K3.ofLimbs [0, 0, 0], nCoins := #[], derived := #[], tabs := tab9 famJ9A ps,
    pubIn := PE.toy1Claim, pubLay := (match layoutOfTabsF famJ9A.tabOf famJ9A.tabLens (tab9 famJ9A ps) with | .ok L => L | .error _ => ⟨#[], #[], #[]⟩),
    slotOf := PE.idSlots, pubMode := famJ9A.pubMode }

open NockvmE2E.Exec.J9AChips in
def pubWitness9 : Bool :=
  -- the layout builder succeeds on the 8 chip ids and equals `layoutOf9`
  (match layoutOfTabsF famJ9A.tabOf famJ9A.tabLens (tab9 famJ9A PE.toy9On) with | .ok L => L.bases == (PE.layoutOf9 PE.toy9On).bases && L.present == #[true,true,true,true,true,true,true,true] && L.lens == PE.tabLens9 | .error _ => false) &&
  (instOf9 PE.toy9On).pubMode == 2 &&
  (instOf9 PE.toy9On).pubCheck PE.toy1Slots (PE.concatPubs PE.toy9On) &&
  (instOf9 PE.toy9Pubs).pubCheck PE.toy1Slots (PE.concatPubs PE.toy9Pubs) &&
  !(instOf9 PE.toy9On).pubCheck PE.toy1Slots (PE.concatPubs (PE.tweak9 PE.toy9On 6 1)) &&
  !(instOf9 PE.toy9On).pubCheck PE.toy1Slots (PE.concatPubs (PE.tweak9 PE.toy9On 7 0)) &&
  !(instOf9 PE.toy9On).pubCheck PE.toy1Slots (PE.concatPubs (PE.tweak9 PE.toy9On 0 27)) &&
  -- a J-8 (pubMode 0) instance with the same data is NOT the same relation: it rejects the 8-table concat (wrong layout size)
  !({ instOf9 PE.toy9On with pubMode := 0 }).pubCheck PE.toy1Slots (PE.concatPubs PE.toy9On)

theorem pubWitness9_true : pubWitness9 = true := by decide +kernel

end NockvmE2E.Exec.FlatFam

#print axioms NockvmE2E.Exec.FlatFam.layoutOfTabsF_famJ8
#print axioms NockvmE2E.Exec.FlatFam.pubWitness9_true
