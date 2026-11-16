/-
  NockvmE2E/Exec/J9AChipsFam.lean

  `famJ9A : Fam`: the J-9 A chip family = the six J-8 chips with the compute chip replaced by the twin `computeChipVCLHX9`
  (137 columns, preprocessed `17, 18`, rounds `![83, 54]`) plus the optional `axisChipJ9` (52 columns, pre `0, 1`, base round 0 / 𝕂-roles
  round 2) and `splitChipJ9` (90 columns, pre `0, 1`, base 72 / roles round 2).  Public tables (limbs): compute 33, cell 18, walkJ8 24, jet 12,
  atom 36, walkAtom 24, axis 12 (4 𝕂: `pubAXs/pubAXp` Re,Im), split 6 (2 𝕂: `pubSPs` Re,Im).  Sum 165 = the measured public width (`pubCap`).
  Literals: compute9 (numeral 0), axis (0), split at nA ∈ {1, 2} (the atom-table row count is baked into one gate; other nA need a literal + tie).
-/
import NockvmE2E.Exec.ShapeF
import NockvmE2E.Exec.J9AChips
import NockvmE2E.Exec.J8ChipsK_walkJ8_3

set_option autoImplicit false

namespace NockvmE2E.Exec.J9AChips
open NockvmE2E.Exec.J8ChipsK (chipWalkJ8_3)
open NockvmE2E.Exec NockvmE2E.Exec.Tr NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J8Shape NockvmE2E.Exec.J8Chips

def idsJ9A : List String :=
  ["computeChipVCLHX9", "cellChipHQKW", "walkChipJ8", "atomChipHQL", "walkChipHQK", "jetChipJ8", "axisChipJ9", "splitChipJ9"]

def preIdx9 (id : String) : Array Nat :=
  if id == "computeChipVCLHX9" then #[17, 18]
  else if id == "axisChipJ9" || id == "splitChipJ9" then #[0, 1]
  else preIdxJ8 id

def wJ9A (id : String) : Nat :=
  if id == "computeChipVCLHX9" then 137 else if id == "axisChipJ9" then 52 else if id == "splitChipJ9" then 90 else wJ8 id

def colR9 (id : String) (c : Nat) : Nat :=
  if id == "computeChipVCLHX9" then (if c < 83 then 0 else 1)
  else if id == "axisChipJ9" then (if c < 22 then 0 else 2)
  else if id == "splitChipJ9" then (if c < 72 then 0 else 2)
  else colRB id c

def tabOf9 (id : String) : Option Nat :=
  if id == "computeChipVCLHX9" then some 0 else if id == "cellChipHQKW" then some 1 else if id == "walkChipJ8" then some 2
  else if id == "jetChipJ8" then some 3 else if id == "atomChipHQL" then some 4 else if id == "walkChipHQK" then some 5
  else if id == "axisChipJ9" then some 6 else if id == "splitChipJ9" then some 7 else none

def tabLens9 : Array Nat := #[33, 18, 24, 12, 36, 24, 12, 6]

def lits9 (id : String) : List (Nat × Chip) := if id == "computeChipVCLHX9" || id == "axisChipJ9" || id == "splitChipJ9" then expectedOf9 id
  else if id == "walkChipJ8" then expectedOf id ++ [(3, chipWalkJ8_3)] else expectedOf id

def famJ9A : Fam where
  ids := idsJ9A
  mandatory := ["computeChipVCLHX9", "cellChipHQKW", "walkChipJ8", "atomChipHQL"]
  preIdx := preIdx9
  widthOf := wJ9A
  colR := colR9
  tabOf := tabOf9
  tabLens := tabLens9
  lits := lits9
  pubCap := 165
  pubMode := 2

/-- measured: the public width is the sum of the table lengths -/
theorem tabLens9_sum : tabLens9.toList.sum = 165 := by decide
/-- the J-9 A interface has 1273 columns; the cap `(1273 + npub) · 2 + 9 ≤ 2^12` allows `npub ≤ 770` -/
theorem pubCap_ok : (1273 + famJ9A.pubCap) * 2 + 9 ≤ 2 ^ 12 := by decide
theorem widths_sum : (137 + 242 + 166 + 71 + 349 + 166 + 52 + 90 : ℕ) = 1273 := by decide
theorem famJ9A_widths : (idsJ9A.map wJ9A).sum = 137 + 242 + 166 + 349 + 166 + 71 + 52 + 90 := by decide
/-- every id of the family has a public table, and distinct ones -/
theorem tabOf9_ids : idsJ9A.map tabOf9 = [some 0, some 1, some 2, some 4, some 5, some 3, some 6, some 7] := by decide
/-- vacuity: J-8 chip data are literally the J-8 ones off the three new ids -/
theorem famJ9A_j8 (id : String) (h1 : id ≠ "computeChipVCLHX9") (h2 : id ≠ "axisChipJ9") (h3 : id ≠ "splitChipJ9") :
    famJ9A.widthOf id = famJ8.widthOf id ∧ famJ9A.preIdx id = famJ8.preIdx id ∧ famJ9A.colR id = famJ8.colR id := by
  refine ⟨?_, ?_, ?_⟩
  · simp [famJ9A, famJ8, wJ9A, h1, h2, h3]
  · simp [famJ9A, famJ8, preIdx9, h1, h2, h3]
  · funext c; simp [famJ9A, famJ8, colR9, h1, h2, h3]

end NockvmE2E.Exec.J9AChips

#print axioms NockvmE2E.Exec.J9AChips.pubCap_ok
#print axioms NockvmE2E.Exec.J9AChips.tabLens9_sum
#print axioms NockvmE2E.Exec.J9AChips.famJ9A_j8
