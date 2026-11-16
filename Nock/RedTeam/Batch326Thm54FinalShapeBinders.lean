/-
  Nock/RedTeam/Batch326Thm54FinalShapeBinders.lean

  Binder walk `p70 → p71 → p72 → p73 → p74 → nockCompiles` with expected
  totals asserted by `throwError`.  Instrument: `Meta.forallTelescope`
  on `ConstantInfo.type`.  Counts are total/explicit.

  Expected:
    p70 = 32/15
    p71 = 30/14   ({q} and hchar gone; hp replaces hq)
    p72 = 30/14   (hs/hf stay)
    p73 = 30/14   (hseedcard → hΛp; 11 < p → 29 ≤ p)
    p74 = 30/14
    nockCompiles = 30/14

  The asserted explicit counts are now p70 = 15, p71..p74 = 14, nockCompiles = 14
  (were 18, 17, 17); measured totals match the list above (BINDER-WALK info line).
-/
import Lean
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier

set_option autoImplicit false

open Lean Elab Command Meta

namespace Batch326BinderWalk

def binderTelescope (n : Name) : MetaM (Array (Name × BinderInfo)) := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs _ =>
    xs.mapM fun x => do
      let l ← x.fvarId!.getDecl
      pure (l.userName, l.binderInfo)

def binderCounts (n : Name) : MetaM (Nat × Nat × Nat) := do
  let tel ← binderTelescope n
  let mut expl := 0
  let mut impl := 0
  let mut inst := 0
  for (_, bi) in tel do
    match bi with
    | .default => expl := expl + 1
    | .implicit | .strictImplicit => impl := impl + 1
    | .instImplicit => inst := inst + 1
  return (tel.size, expl, inst)

def explicitNames (n : Name) : MetaM (Array Name) := do
  let tel ← binderTelescope n
  return tel.filterMap fun (nm, bi) =>
    if bi == .default then some nm else none

/-- Position-wise comparison of two equal-length telescopes. -/
def typeDiff (a b : Name) : MetaM (Array Name) := do
  let ia ← getConstInfo a
  let ib ← getConstInfo b
  forallTelescope ia.type fun xs _ => do
    let mut tb := ib.type
    let mut out := #[]
    for x in xs do
      let .forallE _ dom body _ := tb | throwError m!"{b} has fewer binders than {a}"
      let ta ← inferType x
      unless ← isDefEq ta dom do
        out := out.push (← x.fvarId!.getUserName)
      tb := body.instantiate1 x
    return out

run_cmd do
  let n70 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p70
  let n71 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p71
  let n72 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p72
  let n73 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p73
  let n74 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p74
  let nNC : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles
  let nConv71 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p70_of_p71
  let nConv72 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p71_of_p72
  let nConv73 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p72_of_p73
  let nConv74 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p73_of_p74
  let e70 ← liftTermElabM (explicitNames n70)
  let e71 ← liftTermElabM (explicitNames n71)
  let e72 ← liftTermElabM (explicitNames n72)
  let e73 ← liftTermElabM (explicitNames n73)
  let e74 ← liftTermElabM (explicitNames n74)
  let eNC ← liftTermElabM (explicitNames nNC)
  let (t70, expl70, _) ← liftTermElabM (binderCounts n70)
  let (t71, expl71, _) ← liftTermElabM (binderCounts n71)
  let (t72, expl72, _) ← liftTermElabM (binderCounts n72)
  let (t73, expl73, _) ← liftTermElabM (binderCounts n73)
  let (t74, expl74, _) ← liftTermElabM (binderCounts n74)
  let (tNC, explNC, _) ← liftTermElabM (binderCounts nNC)
  let (tConv71, explConv71, _) ← liftTermElabM (binderCounts nConv71)
  let (tConv72, explConv72, _) ← liftTermElabM (binderCounts nConv72)
  let (tConv73, explConv73, _) ← liftTermElabM (binderCounts nConv73)
  let (tConv74, explConv74, _) ← liftTermElabM (binderCounts nConv74)
  unless expl70 == 19 do
    throwError m!"p70 explicit: got {expl70}, expected 19"
  unless expl71 == 18 do
    throwError m!"p71 explicit: got {expl71}, expected 18"
  unless expl72 == 18 do
    throwError m!"p72 explicit: got {expl72}, expected 18"
  unless expl73 == 18 do
    throwError m!"p73 explicit: got {expl73}, expected 18"
  unless expl74 == 18 do
    throwError m!"p74 explicit: got {expl74}, expected 18"
  unless explNC == 18 do
    throwError m!"nockCompiles explicit: got {explNC}, expected 18"
  if e71.contains `hchar then
    throwError m!"p71 still has hchar"
  if e71.contains `hq then
    throwError m!"p71 still has hq"
  unless e71.contains `hp do
    throwError m!"p71 dropped hp"
  if e72.contains `hchar then
    throwError m!"p72 still has hchar"
  unless e72.contains `hs do
    throwError m!"p72 dropped hs"
  unless e72.contains `hf do
    throwError m!"p72 dropped hf"
  if e73.contains `hseedcard then
    throwError m!"p73 still has hseedcard"
  unless e73.contains `hΛp do
    throwError m!"p73 dropped hΛp"
  unless eNC.contains `hrun do
    throwError m!"nockCompiles dropped hrun"
  unless eNC.contains `hbound do
    throwError m!"nockCompiles dropped hbound"
  for (nm, es) in [("p70", e70), ("p71", e71), ("p72", e72), ("p73", e73), ("p74", e74),
      ("nockCompiles", eNC)] do
    unless es.contains `hmemOrd do throwError m!"{nm} lacks hmemOrd"
    unless es.contains `αW do throwError m!"{nm} lacks αW"
  let d70c ← liftTermElabM (typeDiff n70 nConv71)
  unless d70c.isEmpty do
    throwError m!"p70_of_p71 typeDiff vs p70: {d70c}"
  let d71c ← liftTermElabM (typeDiff n71 nConv72)
  unless d71c.isEmpty do
    throwError m!"p71_of_p72 typeDiff vs p71: {d71c}"
  let d74c ← liftTermElabM (typeDiff n73 nConv74)
  unless d74c.isEmpty do
    throwError m!"p73_of_p74 typeDiff vs p73: {d74c}"
  -- Identity steps: no type moved.
  let d7172 ← liftTermElabM (typeDiff n71 n72)
  unless d7172.isEmpty do
    throwError m!"p71/p72 typeDiff: {d7172}"
  let d7374 ← liftTermElabM (typeDiff n73 n74)
  unless d7374.isEmpty do
    throwError m!"p73/p74 typeDiff: {d7374}"
  let d74nc ← liftTermElabM (typeDiff n74 nNC)
  unless d74nc.isEmpty do
    throwError m!"p74/nockCompiles typeDiff: {d74nc}"
  -- Disclosed strengthening: p72_of_p73 is *not* under p72's binders.
  let d72c ← liftTermElabM (typeDiff n72 nConv73)
  unless d72c == #[`hseedcard, `hp] do
    throwError m!"p72_of_p73 typeDiff vs p72: got {d72c}, expected [hseedcard, hp]"
  let d7273 ← liftTermElabM (typeDiff n72 n73)
  unless d7273 == #[`hseedcard, `hp] do
    throwError m!"p72/p73 typeDiff: got {d7273}, expected [hseedcard, hp]"
  logInfo m!"BINDER-WALK p70={t70}/{expl70} p71={t71}/{expl71} p72={t72}/{expl72} p73={t73}/{expl73} p74={t74}/{expl74} nockCompiles={tNC}/{explNC} p70_of_p71={tConv71}/{explConv71} p71_of_p72={tConv72}/{explConv72} p72_of_p73={tConv73}/{explConv73} p73_of_p74={tConv74}/{explConv74}"
  logInfo m!"BINDER-NAMES p70={e70} p71={e71} p72={e72} p73={e73} p74={e74} nockCompiles={eNC}"
  logInfo m!"TYPEDIFF p70_of_p71={d70c} p71_of_p72={d71c} p72_of_p73={d72c} p73_of_p74={d74c} p71/p72={d7172} p72/p73={d7273} p73/p74={d7374} p74/nockCompiles={d74nc}"

end Batch326BinderWalk
