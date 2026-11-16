/-
  NockvmE2E/Exec/ChipShapeL.lean

  List twins of `chipCanon` / `chipNo63` / `chipReadsLtB` (the chip conjuncts of `j8ShapeOk`) with bridge lemmas (`Array.all_toList`), and the kernel facts
  for the J8Chips literals that toy1 uses (compute, cell, walkJ8 at kroots 1, atom).  `Array.all` over a big literal is well-founded in the kernel
  (`chipCanon chipAtom` > 16 GB, no result in 10 min); the structural list twins are cheap.  `j8ShapeOk` is NOT edited.
-/
import NockvmE2E.Exec.J8Chips
import NockvmE2E.Exec.J8ShapeB

set_option autoImplicit false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.ChipShapeL
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J8Shape

def chipCanonL (c : Tr.Chip) : Bool := c.shared.toList.all exCanon && c.cons.toList.all (fun k => exCanon k.e)
def chipNo63L (c : Tr.Chip) : Bool := c.shared.toList.all exNo63 && c.cons.toList.all (fun k => exNo63 k.e)
def chipReadsLtL (ch : Tr.Chip) (w npub nch : Nat) : Bool :=
  ch.shared.toList.all (exReadsLtB w npub nch ch.baseCols) && ch.cons.toList.all (fun c => exReadsLtB w npub nch ch.baseCols c.e)

theorem chipCanon_eq (c : Tr.Chip) : chipCanon c = chipCanonL c := by
  simp only [chipCanon, chipCanonL, Array.all_toList]
theorem chipNo63_eq (c : Tr.Chip) : chipNo63 c = chipNo63L c := by
  simp only [chipNo63, chipNo63L, Array.all_toList]
theorem chipReadsLt_eq (c : Tr.Chip) (w npub nch : Nat) : chipReadsLtB c w npub nch = chipReadsLtL c w npub nch := by
  simp only [chipReadsLtB, chipReadsLtL, Array.all_toList]

/-- the K tags are not read -/
theorem canonL_tags (c : Tr.Chip) (a b : Array Bool) : chipCanonL { c with sharedK := a, consK := b } = chipCanonL c := rfl
theorem no63L_tags (c : Tr.Chip) (a b : Array Bool) : chipNo63L { c with sharedK := a, consK := b } = chipNo63L c := rfl
theorem readsL_tags (c : Tr.Chip) (a b : Array Bool) (w n m : Nat) :
    chipReadsLtL { c with sharedK := a, consK := b } w n m = chipReadsLtL c w n m := rfl

theorem compute_canon : chipCanonL chipCompute = true := by decide +kernel
theorem compute_no63 : chipNo63L chipCompute = true := by decide +kernel
theorem compute_reads : chipReadsLtL chipCompute 123 33 19 = true := by decide +kernel
theorem cell_canon : chipCanonL chipCell = true := by decide +kernel
theorem cell_no63 : chipNo63L chipCell = true := by decide +kernel
theorem cell_reads : chipReadsLtL chipCell 242 18 19 = true := by decide +kernel
theorem walk1_canon : chipCanonL chipWalkJ8_1 = true := by decide +kernel
theorem walk1_no63 : chipNo63L chipWalkJ8_1 = true := by decide +kernel
theorem walk1_reads : chipReadsLtL chipWalkJ8_1 166 24 19 = true := by decide +kernel
theorem atom_canon : chipCanonL chipAtom = true := by decide +kernel
theorem atom_no63 : chipNo63L chipAtom = true := by decide +kernel
theorem atom_reads : chipReadsLtL chipAtom 349 36 19 = true := by decide +kernel

end NockvmE2E.Exec.ChipShapeL

#print axioms NockvmE2E.Exec.ChipShapeL.atom_canon
#print axioms NockvmE2E.Exec.ChipShapeL.atom_no63
#print axioms NockvmE2E.Exec.ChipShapeL.atom_reads
#print axioms NockvmE2E.Exec.ChipShapeL.cell_reads
#print axioms NockvmE2E.Exec.ChipShapeL.compute_reads
#print axioms NockvmE2E.Exec.ChipShapeL.walk1_reads
#print axioms NockvmE2E.Exec.ChipShapeL.chipReadsLt_eq
