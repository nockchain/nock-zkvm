/-
(core, no `ShapeF`/E2E imports): the generic parser under `loadInstF F path` (`FlatFam.lean`), the family-generic instance loader.  `Flat.loadInst` fixes six tables (`PE.tabOfId`) and `pubMode = 0`; here the public layout
is read off `F.tabOf` / `F.tabLens` (8 tables for `famJ9A`), chip ids must be in `F.ids`, and `pubMode := F.pubMode`.  Pure parser `parseInstF` (JSON +
already-loaded chips) and a thin IO wrapper.  Kernel lemmas: `layoutOfTabsF famJ8 = layoutOfTabs` (rfl) and the executed-selftest witness
`pubWitness9` (pubMode 2, 8-table layout) accepts the toy vector `toy9On` and the J-8 one and rejects tweaked ones.
-/
import NockvmE2E.Exec.Flat
import NockvmE2E.Exec.PubExe9

set_option autoImplicit false

namespace NockvmE2E.Exec.FlatF
open Lean NockvmE2E.Exec.VF NockvmE2E.Exec.J NockvmE2E.Exec.V

/-- the public layout of a table list for family `F` (`layoutOfTabs` with the table index / lengths from `F`) -/
def layoutOfTabsF (tabOf : String → Option Nat) (tabLens : Array Nat) (tabs : Array TabInst) : Except String PE.PubLayout := do
  let n := tabLens.size
  let mut bases : Array Nat := Array.replicate n 0
  let mut present : Array Bool := Array.replicate n false
  for t in tabs do
    match tabOf t.chip.id with
    | none => throw s!"unknown chip id {t.chip.id}"
    | some i =>
      if present[i]! then throw s!"duplicate table {t.chip.id}"
      if t.npub != tabLens[i]! then throw s!"table {t.chip.id}: {t.npub} publics, expected {tabLens[i]!}"
      bases := bases.set! i t.pubBase
      present := present.set! i true
  pure { bases := bases, lens := tabLens, present := present }

/-- pure parser: instance JSON `j` with the tabs' chips already loaded (`chips[i]` is the chip of `tabs[i]`) -/
def parseInstF (ids : List String) (tabOf : String → Option Nat) (tabLens : Array Nat) (pubMode : Nat) (j : Json) (chips : Array Tr.Chip) : Except String ExecInst := do
  let g (what : String) (x : Json) : Except String G := do pure (UInt64.ofNat (← limbE what x))
  let tj := arr (get j "tabs")
  if tj.size != chips.size then throw "tabs/chips size mismatch"
  let mut tabs : Array TabInst := #[]
  for i in [0:tj.size] do
    let t := tj[i]!
    let some c := chips[i]? | throw "chip index"
    tabs := tabs.push { hN := ← natE "tab.hN" (get t "hN"), col0 := ← natE "tab.col0" (get t "col0"), nc := ← natE "tab.nc" (get t "nc")
                        npub := ← natE "tab.npub" (get t "npub"), pubBase := ← natE "tab.pubBase" (get t "pubBase"), chip := c }
  let pubIn ← pubInE (get j "pubIn")
  let slotOf ← natsE "slotOf" (get j "slotOf")
  for t in tabs do
    if !(ids.contains t.chip.id) then throw s!"chip id {t.chip.id} not in the family"
  let layout ← layoutOfTabsF tabOf tabLens tabs
  pure { nD := ← natE "nD" (get j "nD"), dShift := ← g "dShift" (get j "dShift"), dGen := ← g "dGen" (get j "dGen")
         hN := ← natE "hN" (get j "hN"), hGen := ← g "hGen" (get j "hGen"), hShift := ← g "hShift" (get j "hShift")
         r := ← natE "r" (get j "r"), k := ← natE "k" (get j "k"), d := ← natE "d" (get j "d"), l := ← natE "l" (get j "l")
         nc := ← natE "nc" (get j "nc"), nq := ← natE "nq" (get j "nq")
         colKind := ← natsE "colKind" (get j "colKind"), blockOf := ← natsE "blockOf" (get j "blockOf")
         pre := ← (arr (get j "pre")).mapM fun a => (arr a).mapM (g "pre")
         pubOf := ← natsE "pubOf" (get j "pubOf"), ppt := ← k3E "ppt" (get j "ppt")
         nCoins := ← natsE "nCoins" (get j "nCoins")
         derived := ← (arr (get j "derived")).mapM fun a => do pure (← natE "derived" (arr a)[0]!, ← natE "derived" (arr a)[1]!)
         tabs := tabs, pubIn := pubIn, pubLay := layout, slotOf := slotOf, pubMode := pubMode }

def loadInstG (ids : List String) (tabOf : String → Option Nat) (tabLens : Array Nat) (pubMode : Nat) (path : String) : IO ExecInst := do
  let j ← readJson path
  let chips ← (arr (get j "tabs")).mapM fun t => Tr.loadChip (str (get t "chip"))
  IO.ofExcept ((parseInstF ids tabOf tabLens pubMode j chips).mapError IO.userError)

end NockvmE2E.Exec.FlatF
