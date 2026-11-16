/-
  Nock/RedTeam/Batch2290Thm54MM40Accounting.lean

  * Accounting: the live statement has exactly SIX fields, `1 + 1 + 3 + 1`: `standalone` (at the
    honest-carrying cores `compCoreVSQH` / `memCoreVSQH`), `bound` (`≤ boundVCLHQ''`), `figure_156`,
    `figure_155`, `figure_166`, `completeness` (`vsqCompleteness` at the honest run).  Asserted: the cores'
    `Honest` is `HonestVSQD` (not `Empty`), and `P.CF` / `P.MF` are those cores.
  * `nockCompiles_*` binders: measured and asserted (`nockCompiles_zmod` / `nockCompilesHostile` 25/15,
    `nockCompiles_p76` 28/15, as signed in §1 v7); `hop5` is a binder, `hrowsC` is not.
  * All three carry the honest-acceptance conjunct
    `∀ χ, HonestGoodVSQ … χ → AcceptsG package.verifier … χ`; `nockCompilesHostile`'s hostile conjunct is
    quantified over an arbitrary `V' : VerifierData …`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesVCL
import Nock.NockVMROM.Thm54.Walk39.GenNockCompilesVCL
import Nock.PaperNames

set_option autoImplicit false

namespace Nock.RedTeam.Batch2290

open Lean Meta Elab Command

theorem exact_vsqh_one_one_three_one : (1 + 1 + 3 + 1 : ℕ) = 6 := rfl

run_cmd do
  let env ← getEnv
  let S := `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement
  let fs := getStructureFields env S
  let want : Array Name := #[`standalone, `bound, `figure_156, `figure_155, `figure_166, `completeness]
  unless fs == want do throwError "40th statement fields are not exactly {want}: {fs}"
  let PK := `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage
  let some ci := env.find? (S ++ `standalone) | throwError "no standalone projection"
  let used := ci.type.getUsedConstants
  unless used.contains (PK ++ `CF) && used.contains (PK ++ `MF) do throwError "standalone not at P.CF / P.MF"
  let some cf := env.find? (PK ++ `CF) | throwError "no CF"
  let some mf := env.find? (PK ++ `MF) | throwError "no MF"
  unless (cf.value? (allowOpaque := true)).get!.getUsedConstants.contains `Nock.NockVMROM.Thm54.VclL.Handle.CoresVSQH.compCoreVSQH do
    throwError "P.CF is not compCoreVSQH"
  unless (mf.value? (allowOpaque := true)).get!.getUsedConstants.contains `Nock.NockVMROM.Thm54.VclL.Handle.CoresVSQH.memCoreVSQH do
    throwError "P.MF is not memCoreVSQH"
  for c in [`Nock.NockVMROM.Thm54.VclL.Handle.CoresVSQH.compCoreVSQH, `Nock.NockVMROM.Thm54.VclL.Handle.CoresVSQH.memCoreVSQH] do
    let some k := env.find? c | throwError "missing {c}"
    let u := (k.value? (allowOpaque := true)).get!.getUsedConstants
    unless u.contains `Nock.NockVMROM.Thm54.VclL.Handle.CoresVSQH.HonestVSQD do throwError "{c}: Honest is not HonestVSQD"
    if u.contains `Empty then throwError "{c}: still mentions Empty"
  let tf := getStructureFields env (`Nock.Walk39 ++ S)
  unless tf == #[`standalone, `bound, `figure_155, `figure_154, `figure_164, `completeness] do
    throwError "39th twin fields changed: {tf}"
  logInfo m!"STATEMENT-FIELDS {fs.size} {fs}; standalone at compCoreVSQH / memCoreVSQH (Honest := HonestVSQD)"

/-- Binder census of a declaration (total, Prop, names incl. the `∀` block under a `haveI`). -/
def census (c : Name) : CommandElabM (Nat × Nat × Array String) := do
  let some ci := (← getEnv).find? c | throwError "missing {c}"
  liftTermElabM <| forallTelescope ci.type fun xs body => do
    let mut props : Nat := 0
    let mut nm : Array String := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      let isP ← isProp d.type
      if isP then props := props + 1
      nm := nm.push s!"{d.userName.eraseMacroScopes}{if isP then "*" else ""}"
    let inner ← forallTelescope (← whnfR body) fun ys _ => do
      let mut m : Array String := #[]
      for y in ys do m := m.push s!"{(← y.fvarId!.getDecl).userName.eraseMacroScopes}"
      pure m
    pure (xs.size, props, nm ++ inner)

run_cmd do
  let pre := `Nock.NockVMROM.Thm54.TraceGen.VCL38
  let rows : List (Name × Nat × Nat) := [
    (pre ++ `nockCompiles_zmod, 25, 15),
    (pre ++ `nockCompilesHostile, 25, 15),
    (pre ++ `nockCompiles_p76, 28, 15)]
  for (c, tot, pr) in rows do
    let (n, p, names) ← census c
    logInfo m!"BINDERS {c}: {n}/{p} {names}"
    unless n == tot && p == pr do throwError "binder count of {c} is {n}/{p}, expected {tot}/{pr}"
    unless names.contains "hop5" || names.contains "hop5*" do throwError "{c}: no hop5 binder"
    if names.contains "hrowsC" || names.contains "hrowsC*" then throwError "{c}: hrowsC still a binder"
  for c in [`Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package,
      `Nock.Walk39.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package] do
    let (n, p, _) ← census c
    logInfo m!"CAPSTONE-BINDERS {c}: {n}/{p}"
    unless n == 13 && p == 2 do throwError "capstone binders {n}/{p}, expected 13/2"

/-- The conjuncts of `∃ package, A ∧ B ∧ …` (after the binder telescope and the `haveI` block). -/
partial def conjuncts (e : Expr) : MetaM (Array Expr) := do
  let e ← whnfR e
  if e.isAppOfArity ``And 2 then
    return #[e.appFn!.appArg!] ++ (← conjuncts e.appArg!)
  return #[e]

-- REV40 findings 2.1 / 5.1 : the honest-acceptance conjunct on all three `nockCompiles_*`, and
-- the hostile conjunct of `nockCompilesHostile` over an ARBITRARY verifier datum.
run_cmd do
  let pre := `Nock.NockVMROM.Thm54.TraceGen.VCL38
  for (c, nConj) in [(pre ++ `nockCompiles_zmod, 3), (pre ++ `nockCompilesHostile, 4), (pre ++ `nockCompiles_p76, 3)] do
    let some ci := (← getEnv).find? c | throwError "missing {c}"
    let ok ← liftTermElabM <| forallTelescope ci.type fun _ body => do
      let b ← whnfR body
      forallTelescope b fun _ ex => do
        let ex ← whnfR ex
        unless ex.isAppOfArity ``Exists 2 do throwError "{c}: conclusion is not ∃ package"
        lambdaTelescope ex.appArg! fun _ conj => do
          let cs ← conjuncts conj
          unless cs.size == nConj do throwError "{c}: {cs.size} conjuncts, expected {nConj}"
          let acc := cs[2]!.getUsedConstants
          unless acc.contains `Nock.NockVMROM.Thm54.SVFrameG.AcceptsG &&
              acc.contains `Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ.HonestGoodVSQ do
            throwError "{c}: third conjunct is not honest acceptance off HonestGoodVSQ"
          if nConj == 4 then
            -- the hostile conjunct: `∀ (V' : VerifierData …) msg, …` (its first binder is a verifier datum,
            -- not the package's own verifier)
            let h ← whnfR cs[3]!
            match h with
            | .forallE _ ty _ _ =>
              unless ty.getAppFn.constName? == some `Nock.NockVMROM.Thm54.SVFrame.VerifierData do
                throwError "{c}: hostile conjunct is not over an arbitrary VerifierData: {ty}"
            | _ => throwError "{c}: hostile conjunct is not a ∀"
          pure true
    logInfo m!"CONCLUSION {c}: acceptance conjunct present{if nConj == 4 then "; hostile ∀ V'" else ""} ({ok})"

run_cmd do
  let env ← getEnv
  let live := `Nock.Walk39.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
  let rep := `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
  let some b := env.find? live | throwError "no 39th twin capstone"
  let some a := env.find? rep | throwError "no live capstone"
  let pp (e : Expr) : CommandElabM String := liftTermElabM <|
    withOptions (fun o => (o.setBool `pp.all true).setBool `pp.universes true) do
      return toString (← ppExpr e)
  -- compare modulo whitespace: the longer twin name changes only the pretty-printer's line wrapping
  let norm (s : String) : String := Id.run do
    let mut out := ""
    let mut ws := false
    for c in s.toList do
      if c.isWhitespace then ws := true
      else
        if ws && !out.isEmpty then out := out.push ' '
        ws := false
        out := out.push c
    return out
  let sa := norm (← pp a.type)
  let sb := norm (← pp b.type)
  let sb' := sb.replace "Nock.Walk39." ""
  unless sb != sa do throwError "twin type printed identically before the rename (rename instrument void)"
  unless sa == sb' do throwError "live capstone type differs from the 39th twin's after the rename:\n{sa}\n---\n{sb'}"
  logInfo m!"FINGERPRINT-INPUT equal after rename ({sa.length} chars)"

end Nock.RedTeam.Batch2290

#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompiles_zmod
#print axioms Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompilesHostile
#print axioms Nock.NockVMROM.Thm54.TraceGen.VCL38.nockCompiles_p76
#print axioms Nock.NockVMROM.Thm54.TraceGen.VCL38.pkgOfRun_accepted
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.CoresVSQH.standaloneVSQH
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.CoresVSQH.standaloneVSQH_completeness_le
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.CoresVSQH.prob_not_good_le
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.CoresVSQH.epsilon_honestBad
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.CoresVSQH.fig_of_bound
#print axioms «Thm:NockVMROM»
#print axioms Nock.RedTeam.Batch2290.exact_vsqh_one_one_three_one
