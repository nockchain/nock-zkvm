/-
  Nock/RedTeam/Batch2293Thm54MM40DeadBinders.lean

  **REV40 vacuity finding 5.1 repaired — `hs` / `hf` are LIVE.**
  The three theorems now conclude the honest-acceptance
  conjunct (`pkgOfRun_accepted`, which consumes `hs` / `hf` through `hat_of_run`).  Asserted here, on the
  elaborated PROOF TERMS (`value?` with `allowOpaque := true`, opened by `lambdaTelescope`): the binders
  named `hs` and `hf` occur in each body.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesVCL
import Nock.NockVMROM.Thm54.Walk39.GenNockCompilesVCL

set_option autoImplicit false

namespace Nock.RedTeam.Batch2293

open Lean Meta Elab Command

/-- Which of the named binders occur in the body of `c`'s proof term. -/
def occurring (c : Name) (names : List String) : CommandElabM (List (String × Bool)) := do
  let some ci := (← getEnv).find? c | throwError "missing {c}"
  let some v := ci.value? (allowOpaque := true) | throwError "{c}: no value"
  liftTermElabM <| lambdaTelescope v fun xs body => do
    let mut out : List (String × Bool) := []
    for nm in names do
      let mut found := false
      let mut seen := false
      for x in xs do
        let d ← x.fvarId!.getDecl
        if d.userName.eraseMacroScopes.toString == nm then
          seen := true
          -- occurs in the body, or in the type of a LATER binder (it is consumed either way)
          if body.containsFVar x.fvarId! then found := true
      unless seen do throwError "{c}: no binder named {nm}"
      out := out ++ [(nm, found)]
    pure out

run_cmd do
  let pre := `Nock.NockVMROM.Thm54.TraceGen.VCL38
  for c in [pre ++ `nockCompiles_p76, pre ++ `nockCompiles_zmod, pre ++ `nockCompilesHostile] do
    let r ← occurring c ["hs", "hf", "hrun"]
    logInfo m!"OCCURS {c}: {r}"
    for (nm, b) in r do
      unless b do throwError "{c}: binder {nm} does not occur in the proof term (dead)"
  let r ← occurring (`Nock.Walk39 ++ pre ++ `nockCompiles_p76) ["hs", "hf", "hrun"]
  logInfo m!"OCCURS (39th twin, negative control) {r}"
  unless r == [("hs", false), ("hf", false), ("hrun", true)] do
    throwError "negative control did not reproduce the 39th's dead hs / hf: {r}"

end Nock.RedTeam.Batch2293

#print axioms Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompiles_p76
#print axioms Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompiles_zmod
#print axioms Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompilesHostile
