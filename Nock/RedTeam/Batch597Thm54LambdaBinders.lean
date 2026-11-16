/-
  Nock/RedTeam/Batch597Thm54LambdaBinders.lean
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch597

open Lean Meta Elab Command

/-- Walk the Π-telescope of a constant's type: (name, isExplicit) for every binder, plus the body. -/
def telescope (n : Name) : MetaM (Array (Name × Bool) × Expr) := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs body => do
    let mut out := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      out := out.push (d.userName, d.binderInfo.isExplicit)
    return (out, body)

/-- Does the proof term (value) of `n` mention constant `c`? -/
def valueMentions (n c : Name) : MetaM Bool := do
  let ci ← getConstInfo n
  let v := (ci.value? (allowOpaque := true)).getD (.sort .zero)
  return v.getUsedConstants.contains c

/-- Does the TYPE of `n` mention constant `c`? -/
def typeMentions (n c : Name) : MetaM Bool := do
  let ci ← getConstInfo n
  return ci.type.getUsedConstants.contains c

def chain : List Name :=
  [ ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p68
  , ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p69
  , ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p70
  , ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p71
  , ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p72
  , ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p73
  , ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p74
  , ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p75
  , ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76
  , ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod ]

-- Check 1–3: binder inventory, `hax`/`hwidth` absence (binders and Π-premises), `hp64` placement.
run_cmd do
  for n in chain do
    let (bs, body) ← liftTermElabM (telescope n)
    let names := bs.map (·.1)
    let expl := (bs.filter (·.2)).map (·.1)
    for bad in [`hwidth, `hax] do
      if names.contains bad then throwError m!"{n}: elaborated type still carries `{bad}`"
    for (nm, _) in bs do
      if nm.isAnonymous || nm.toString.startsWith "a✝" then
        throwError m!"{n}: anonymous Π-binder {nm} — an inferred-type leak"
    unless expl.contains `lmb do throwError m!"{n}: no explicit `lmb`"
    unless expl.contains `hp64 do throwError m!"{n}: no explicit `hp64`"
    let l := expl.toList
    match l.idxOf? `hp64 with
    | none => throwError m!"{n}: hp64 missing from explicit list"
    | some i =>
        let prev := l[i - 1]!
        unless prev == `hp || prev == `hchar do
          throwError m!"{n}: hp64 follows `{prev}`, not `hp`/`hchar`"
    match l.idxOf? `lmb with
    | none => throwError m!"{n}: lmb missing"
    | some i => unless l[i - 1]! == `αW && l[i - 2]! == `α do
        throwError m!"{n}: lmb does not follow α αW: {l}"
    if body.isForall then throwError m!"{n}: conclusion is still a Π: {body}"
    logInfo m!"{n}: total {bs.size} / explicit {expl.size}; explicit = {expl}"

-- /-- Check 1 (counts): zmod 26/13, p76 28/13; live baseline 24/11 plus exactly `lmb`, `hp64`.
run_cmd do
  let nZ := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
  let n76 := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76
  let (bz, _) ← liftTermElabM (telescope nZ)
  let (b76, _) ← liftTermElabM (telescope n76)
  let ez := ((bz.filter (·.2)).map (·.1)).toList
  let e76 := ((b76.filter (·.2)).map (·.1)).toList
  unless bz.size == 27 ∧ ez.length == 14 do
    throwError m!"zmod counts {bz.size}/{ez.length}, expected 27/14"
  unless b76.size == 31 ∧ e76.length == 16 do
    throwError m!"p76 counts {b76.size}/{e76.length}, expected 31/16 (H1.5b Part 2a: + hrows; the 36th: + hFprime; S2: + αW)"
  let liveZ : List Name := [`α, `hrun, `hbound, `hs, `hf, `hΛp, `hp, `hK, `hF, `hwin, `hKszChar]
  unless ez.filter (fun x => !liveZ.contains x) == [`αW, `lmb, `hp64] do
    throwError m!"zmod new explicit binders are not exactly [αW, lmb, hp64]: {ez}"
  unless ez == [`α, `αW, `lmb, `hrun, `hbound, `hs, `hf, `hΛp, `hp, `hp64, `hK, `hF, `hwin, `hKszChar] do
    throwError m!"zmod explicit order: {ez}"
  logInfo m!"zmod {bz.size}/{ez.length} = live 24/11 + [lmb, hp64]; p76 {b76.size}/{e76.length}"

-- Check 4: conclusion head and conjuncts; no `Classical.skolem` / `Classical.choose` family in
-- the chain's proof terms; the conclusion mentions the package type and the three conjunct shapes.
run_cmd do
  for n in chain do
    let (_, body) ← liftTermElabM (telescope n)
    -- head: ∃ package : OptimizedFullStrictNockVMROMPackage …
    unless body.getAppFn.isConstOf ``Exists do throwError m!"{n}: head is not ∃: {body}"
    let args := body.getAppArgs
    let pkgTy := args[0]!
    unless pkgTy.getUsedConstants.contains
        ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage do
      throwError m!"{n}: ∃ is not over OptimizedFullStrictNockVMROMPackage: {pkgTy}"
    if pkgTy.isForall then throwError m!"{n}: ∃ ranges over a FUNCTION type (family form): {pkgTy}"
    let cs := body.getUsedConstants
    unless cs.contains ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement do
      throwError m!"{n}: conclusion lacks OptimizedFullStrictThm54Statement"
    unless cs.contains ``Nock.NockVMROM.Thm54.ChallengeVector.lam do
      throwError m!"{n}: conclusion lacks the `lam = lmb` conjunct"
    if ← liftTermElabM (valueMentions n ``Classical.skolem) then
      throwError m!"{n}: proof uses Classical.skolem (family form)"
    if ← liftTermElabM (typeMentions n ``Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace.FormRWidth) then
      throwError m!"{n}: TYPE mentions FormRWidth"
    if ← liftTermElabM (typeMentions n ``Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace.FormRAxisBound) then
      throwError m!"{n}: TYPE mentions FormRAxisBound"
  logInfo m!"chain: ∃ package : Pkg (not a family), Stmt ∧ claim ∧ lam = lmb; no skolem; no FormRWidth/FormRAxisBound in types"

-- Positive control for `valueMentions`: `nockCompiles_p68`'s proof DOES mention
-- `FormRWidth_of_hp64` (the lemma replacing the binder) — so absence claims above are not
-- vacuous instrument failures.
run_cmd do
  let n := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p68
  let okW ← liftTermElabM (valueMentions n ``Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda.FormRWidth_of_hp64)
  let okA ← liftTermElabM (valueMentions n ``Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda.genComputeRows_rowsFormRAxisBound)
  unless okW do throwError "positive control failed: p68 proof does not mention FormRWidth_of_hp64"
  unless okA do throwError "positive control failed: p68 proof does not mention genComputeRows_rowsFormRAxisBound"
  logInfo m!"positive control: p68 proof mentions FormRWidth_of_hp64 and genComputeRows_rowsFormRAxisBound"

#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76

end Nock.RedTeam.Batch597
