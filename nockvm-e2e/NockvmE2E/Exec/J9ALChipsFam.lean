/-
  NockvmE2E/Exec/J9ALChipsFam.lean   (Mathlib-free)

  `famJ9AL : Fam`: the J-9 AL chip family = `famJ9A` + the optional ALU `aluChipJ9` (196 columns = 94 base + 18 + 16 𝕂 columns; preprocessed `0..4` =
  masks `0, 1` and the preg layout `sP, pId, pOp`; commit rounds `0 / 1 / 2` at `94 / 148`; public table 8 with 18 limbs = 6 K3).
  Public tables (limbs) `33, 18, 24, 12, 36, 24, 12, 6, 18`, sum 183 (`pubCap`); `pubMode = 3` (`PE.pubCheck9L`).
  `shapeOkF` / `shapeXOkF` / `chipsOkF` are the unchanged definitions, only the `Fam` value is new.
-/
import NockvmE2E.Exec.J9AChipsFam
import NockvmE2E.Exec.J9ALChips
import NockvmE2E.Exec.PubExe9L

set_option autoImplicit false

namespace NockvmE2E.Exec.J9ALChips
open NockvmE2E.Exec NockvmE2E.Exec.Tr NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips

def idsJ9AL : List String := idsJ9A ++ ["aluChipJ9"]

def preIdxAL (id : String) : Array Nat := if id == "aluChipJ9" then #[0, 1, 2, 3, 4] else preIdx9 id

def wJ9AL (id : String) : Nat := if id == "aluChipJ9" then 196 else wJ9A id

def colRAL (id : String) (c : Nat) : Nat :=
  if id == "aluChipJ9" then (if c < 94 then 0 else if c < 148 then 1 else 2) else colR9 id c

def tabOfAL (id : String) : Option Nat := if id == "aluChipJ9" then some 8 else tabOf9 id

def tabLensAL : Array Nat := tabLens9.push 18

def litsAL (id : String) : List (Nat × Chip) := if id == "aluChipJ9" then [(0, chipAlu)] else lits9 id

def famJ9AL : Fam where
  ids := idsJ9AL
  mandatory := ["computeChipVCLHX9", "cellChipHQKW", "walkChipJ8", "atomChipHQL"]
  preIdx := preIdxAL
  widthOf := wJ9AL
  colR := colRAL
  tabOf := tabOfAL
  tabLens := tabLensAL
  lits := litsAL
  pubCap := 183
  pubMode := 3

theorem tabLensAL_sum : tabLensAL.toList.sum = 183 := by decide
theorem tabLensAL_eq_pe : tabLensAL = NockvmE2E.Exec.PE.tabLens9L := by decide
theorem pubCapAL_ok : (1273 + 196 + famJ9AL.pubCap) * 2 + 9 ≤ 2 ^ 12 := by decide
theorem tabOfAL_ids : idsJ9AL.map tabOfAL = [some 0, some 1, some 2, some 4, some 5, some 3, some 6, some 7, some 8] := by decide
/-- off the ALU, the family data are those of `famJ9A` -/
theorem famJ9AL_j9a (id : String) (h : id ≠ "aluChipJ9") :
    famJ9AL.widthOf id = famJ9A.widthOf id ∧ famJ9AL.preIdx id = famJ9A.preIdx id ∧ famJ9AL.colR id = famJ9A.colR id ∧
    famJ9AL.tabOf id = famJ9A.tabOf id ∧ famJ9AL.lits id = famJ9A.lits id := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [famJ9AL, famJ9A, wJ9AL, h]
  · simp [famJ9AL, famJ9A, preIdxAL, h]
  · funext c; simp [famJ9AL, famJ9A, colRAL, h]
  · simp [famJ9AL, famJ9A, tabOfAL, h]
  · simp [famJ9AL, famJ9A, litsAL, h]
/-- the ALU data -/
theorem famJ9AL_alu : famJ9AL.widthOf "aluChipJ9" = 196 ∧ famJ9AL.preIdx "aluChipJ9" = #[0, 1, 2, 3, 4] ∧
    (famJ9AL.colR "aluChipJ9" 93 = 0 ∧ famJ9AL.colR "aluChipJ9" 94 = 1 ∧ famJ9AL.colR "aluChipJ9" 147 = 1 ∧ famJ9AL.colR "aluChipJ9" 148 = 2 ∧
      famJ9AL.colR "aluChipJ9" 195 = 2) ∧
    famJ9AL.tabOf "aluChipJ9" = some 8 := by decide
/-- the family literal list of the ALU is the single numeral-0 literal `chipAlu` -/
theorem famJ9AL_alu_lits : famJ9AL.lits "aluChipJ9" = [(0, chipAlu)] := rfl

end NockvmE2E.Exec.J9ALChips

#print axioms NockvmE2E.Exec.J9ALChips.tabLensAL_sum
#print axioms NockvmE2E.Exec.J9ALChips.tabLensAL_eq_pe
#print axioms NockvmE2E.Exec.J9ALChips.pubCapAL_ok
#print axioms NockvmE2E.Exec.J9ALChips.famJ9AL_j9a
#print axioms NockvmE2E.Exec.J9ALChips.famJ9AL_alu
