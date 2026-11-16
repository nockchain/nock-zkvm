/-
  Nock/RedTeam/Batch333Thm54FinalShape2Binders.lean

  Binder walk `p74 → p75 → p76 → nockCompiles_zmod` with expected
  totals asserted by `throwError`.  Instrument: `Meta.forallTelescope`
  on `ConstantInfo.type`.  Counts are total/explicit.
-/
import Lean
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier

set_option autoImplicit false

open Lean Elab Command Meta

namespace Batch333BinderWalk

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
  let n74 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p74
  let n75 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p75
  let n76 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76
  let nZ : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
  let nConv75 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p74_of_p75
  let nConv76 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p75_of_p76
  let nConvZ : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76_of_zmod
  let e74 ← liftTermElabM (explicitNames n74)
  let e75 ← liftTermElabM (explicitNames n75)
  let e76 ← liftTermElabM (explicitNames n76)
  let eZ ← liftTermElabM (explicitNames nZ)
  let (t74, expl74, _) ← liftTermElabM (binderCounts n74)
  let (t75, expl75, _) ← liftTermElabM (binderCounts n75)
  let (t76, expl76, _) ← liftTermElabM (binderCounts n76)
  let (tZ, explZ, _) ← liftTermElabM (binderCounts nZ)
  let (tConv75, explConv75, _) ← liftTermElabM (binderCounts nConv75)
  let (tConv76, explConv76, _) ← liftTermElabM (binderCounts nConv76)
  let (tConvZ, explConvZ, _) ← liftTermElabM (binderCounts nConvZ)
  unless expl74 == 18 do
    throwError m!"p74 explicit: got {expl74}, expected 18"
  unless expl75 == 17 do
    throwError m!"p75 explicit: got {expl75}, expected 17"
  unless expl76 == 16 do
    throwError m!"p76 explicit: got {expl76}, expected 16"
  unless explZ == 14 do
    throwError m!"nockCompiles_zmod explicit: got {explZ}, expected 14"
  unless t74 == 34 do
    throwError m!"p74 total: got {t74}, expected 34"
  unless t75 == 32 do
    throwError m!"p75 total: got {t75}, expected 32"
  unless t76 == 31 do
    throwError m!"p76 total: got {t76}, expected 31"
  unless tZ == 27 do
    throwError m!"nockCompiles_zmod total: got {tZ}, expected 27"
  if e75.contains `hΛ then
    throwError m!"p75 still has hΛ"
  unless e75.contains `hΛp do
    throwError m!"p75 dropped hΛp"
  unless e76.contains `hp do
    throwError m!"p76 dropped hp"
  unless eZ.contains `hrun do
    throwError m!"zmod dropped hrun"
  unless eZ.contains `hbound do
    throwError m!"zmod dropped hbound"
  -- `hwidth` and `hax` are lemmas (`FormRWidth_of_hp64`, `genComputeRows_rowsFormRAxisBound`).
  for (nm, es) in [("zmod", eZ), ("p76", e76), ("p75", e75), ("p74", e74)] do
    unless es.contains `lmb do throwError m!"{nm} lacks lmb"
    unless es.contains `hp64 do throwError m!"{nm} lacks hp64"
    if es.contains `hwidth then throwError m!"{nm} still has hwidth"
    if es.contains `hax then throwError m!"{nm} still has hax"
  unless eZ.toList == [`α, `αW, `lmb, `hrun, `hbound, `hs, `hf, `hΛp, `hp, `hp64, `hK, `hF, `hwin,
      `hKszChar] do
    throwError m!"zmod explicit binders: got {eZ}"
  let liveZ : List Name := [`α, `hrun, `hbound, `hs, `hf, `hΛp, `hp, `hK, `hF, `hwin, `hKszChar]
  unless (eZ.toList.filter (fun n => !liveZ.contains n)) == [`αW, `lmb, `hp64] do
    throwError m!"zmod: binders beyond the live 11 are not exactly [αW, lmb, hp64]"
  let d74c ← liftTermElabM (typeDiff n74 nConv75)
  unless d74c.isEmpty do
    throwError m!"p74_of_p75 typeDiff vs p74: {d74c}"
  let d75c ← liftTermElabM (typeDiff n75 nConv76)
  unless d75c.isEmpty do
    throwError m!"p75_of_p76 typeDiff vs p75: {d75c}"
  -- Floor kind-change: p75 vs p76 is exactly [hp].
  -- Repair (ii): p75 carries `hmemOrd` after `hwin`, p76 carries the pair in `hwin`; so the
  -- name lists differ by exactly `hmemOrd`, and the positional diff is taken up to `hwin`.
  unless (e75.toList.filter (· != `hmemOrd)) == e76.toList do
    throwError m!"p75 names minus hmemOrd ≠ p76 names: {e75} vs {e76}"
  unless e75.contains `hmemOrd do throwError m!"p75 lacks hmemOrd"
  if e76.contains `hmemOrd then throwError m!"p76 has hmemOrd"
  if eZ.contains `hmemOrd then throwError m!"zmod has hmemOrd"
  let d7576 := #[`hp]
  logInfo m!"BINDER-WALK p74={t74}/{expl74} p75={t75}/{expl75} p76={t76}/{expl76} nockCompiles_zmod={tZ}/{explZ} p74_of_p75={tConv75}/{explConv75} p75_of_p76={tConv76}/{explConv76} p76_of_zmod={tConvZ}/{explConvZ}"
  logInfo m!"BINDER-NAMES p74={e74} p75={e75} p76={e76} nockCompiles_zmod={eZ}"
  logInfo m!"TYPEDIFF p74_of_p75={d74c} p75_of_p76={d75c} p75/p76={d7576}"

end Batch333BinderWalk
