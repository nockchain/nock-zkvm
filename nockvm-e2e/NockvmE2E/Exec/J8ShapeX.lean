/-
  NockvmE2E/Exec/J8ShapeX.lean   (Mathlib-free, total)

  `j8ShapeXOk : ExecInst -> Bool`: the four instance facts the J-8 interface tie needs that `j8ShapeOk` (J8ShapeB) does not check:
  `nq = 9`, `npub = pubOf.size ≤ 926`, `blockTabOk` (blockOf of every non-public column = its chip's `colR` round, nock `TraceJ8.cr*`),
  `layOk` (the loader's `pubLay` matches each loaded table, and is `present` exactly for the loaded tables).
  The `*_of_shapeX` Prop lemmas are in `Exec/E2EJ8P.lean`. NOT yet wired into the verifier exe (see the verifier executable).
-/
import NockvmE2E.Exec.J8ShapeB

set_option autoImplicit false

namespace NockvmE2E.Exec.J8Shape
open NockvmE2E.Exec.V

/-- the commit round (Merkle block) of local column `c` of a J-8 chip: twin of nock's `crC crM crW crJ crA` (`TraceJ8.lean:64-72`); `99` for other ids -/
def colRB (id : String) (c : Nat) : Nat :=
  if id == "computeChipVCLHX" then (if c < 69 then 0 else 1)
  else if id == "cellChipHQKW" then (if c < 134 then 0 else if c < 188 then 1 else 2)
  else if id == "walkChipJ8" || id == "walkChipHQK" then (if c < 25 then 0 else if c < 97 then 1 else 2)
  else if id == "jetChipJ8" then (if c < 29 then 0 else 1)
  else if id == "atomChipHQL" then (if c < 205 then 0 else if c < 259 then 1 else 2)
  else 99

def blockTabOk (XI : ExecInst) : Bool :=
  XI.tabs.all (fun t => (List.range (t.nc - t.npub)).all fun c => XI.blockOf[t.col0 + c]! == colRB t.chip.id c)

/-- the loader's public layout matches the loaded tables -/
def layOk (XI : ExecInst) : Bool :=
  XI.pubLay.bases.size == 6 && XI.pubLay.lens.size == 6 && XI.pubLay.present.size == 6 && XI.pubLay.lens == PE.tabLens &&
  XI.tabs.all (fun t => match PE.tabOfId t.chip.id with
    | none => false
    | some i => XI.pubLay.present[i]! && XI.pubLay.bases[i]! == t.pubBase && t.npub == PE.tabLens[i]!) &&
  (List.range 6).all (fun i => XI.pubLay.present[i]! == XI.tabs.any (fun t => PE.tabOfId t.chip.id == some i))

def j8ShapeXOk (XI : ExecInst) : Bool :=
  XI.nq == 9 && decide (XI.pubOf.size ≤ 926) && blockTabOk XI && layOk XI

end NockvmE2E.Exec.J8Shape
