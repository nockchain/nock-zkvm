import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.Language

/-! Meta-level checks that the optimized strict package quantifies and evaluates the memory challenge lambda at the objects' own value. They confirm that `memoryLambdaUniform` is absent, `lam_eq` exists, the containment and fixed-field statement fields quantify `lmb`, and `honestTuple` and `optimizedFailureEvent` read `challenges.lam`. They also re-elaborate the fourth conjunct of `MemoryRowAccepted`. -/
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch599

open Lean Meta Elab Command

-- The field `memoryLambdaUniform` is absent; `lam_eq` exists; Statement fields that must quantify λ do.
run_cmd do
  let env ← getEnv
  let dead := `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.memoryLambdaUniform
  if env.contains dead then throwError m!"memoryLambdaUniform still exists"
  let lamEq := ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.OptimizedSameProblemAt.lam_eq
  unless env.contains lamEq do throwError "lam_eq missing"
  -- Statement fields: `containment`, `p8_fixed_field_soundness`, `p8_fixed_field_bits` take `lmb`
  for f in [ ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement.containment
           , ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement.p8_fixed_field_soundness
           , ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement.p8_fixed_field_bits ] do
    let ci ← getConstInfo f
    let names ← liftTermElabM <| forallTelescope ci.type fun xs body => do
      -- the projection's type ends in the field type; walk that too
      forallTelescope body fun ys _ => do
        let mut ns := #[]
        for y in xs ++ ys do ns := ns.push (← y.fvarId!.getDecl).userName
        return ns
    unless names.contains `lmb do throwError m!"{f} does not quantify lmb: {names}"
    logInfo m!"{f}: binders {names}"
  -- the honest tuple reads the objects' λ, the hostile event is at the objects' λ:
  let ht ← getConstInfo ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.honestTuple
  let v := (ht.value? (allowOpaque := true)).getD (.sort .zero)
  unless v.getUsedConstants.contains ``Nock.NockVMROM.Thm54.ChallengeVector.lam do
    throwError "honestTuple does not read objects.cfg.challenges.lam"
  if v.getUsedConstants.contains ``Nock.MemoryTable.formRDefault then
    throwError "honestTuple still reads formRDefault"
  let fe ← getConstInfo ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.optimizedFailureEvent
  let fv := (fe.value? (allowOpaque := true)).getD (.sort .zero)
  unless fv.getUsedConstants.contains ``Nock.NockVMROM.Thm54.ChallengeVector.lam do
    throwError "optimizedFailureEvent is not evaluated at objects.cfg.challenges.lam"
  logInfo m!"memoryLambdaUniform gone; lam_eq present; honestTuple and optimizedFailureEvent read objects λ"

-- The fourth conjunct of `MemoryRowAccepted` fixes the row's lambda to `cfg.challenges.lam`.
section
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq K]

open Nock.NockVMROM.Thm54 in
example (cfg : ExactConfig F K) (row : Nock.MemoryTable.MState × Nock.MemoryTable.DTmem K)
    (h : ExactExecution.MemoryRowAccepted cfg row) : row.2.2.lambda = cfg.challenges.lam :=
  h.2.2.2
end

#check @Nock.NockVMROM.Thm54.exactLanguage_all_challenges_loadBearing

#check @Nock.NockVMROM.Thm54.ProductionP8Containment.guardedAxisFailureEvent_card_le
#check @Nock.NockVMROM.Thm54.ProductionP8Containment.failureUnion_card_le
#check @Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.p8_fixedField_falseAcceptance_le

end Nock.RedTeam.Batch599
