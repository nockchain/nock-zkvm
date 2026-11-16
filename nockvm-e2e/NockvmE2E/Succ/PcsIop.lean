/-
: `iopPcs`, the honest-oracle-access instance of `PcsBase`
(`iopCS`, `ε_CS = 0`): the DEEP opening plan `deepPlan` over evaluation oracles, no hash, no FRI. Its `sound` is
`rap_succinct_sound_deep` (`Succ/Deep.lean:144`) with the DEEP link `link_deepPlan`. This is the toy instance that
shows `PcsBase` is inhabited by a second, structurally different scheme.
-/
import NockvmE2E.Succ.PcsBase

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open scoped NNReal ENNReal

namespace NockvmE2E.Succ.Pcs

open NockvmE2E.Rap NockvmE2E.Succ NockvmE2E.Deep

variable {Φ : CoinFrame} {F B : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
  [Field B] [Fintype B] [DecidableEq B] [Algebra B F] [Inhabited B] [SampleableType F] [Inhabited F]

/-- The IOP commitment is the column word itself (`iopCS`: `Com := β`); the instances `sRounds` asks for. -/
instance (D : DeepRap Φ F B) : Fintype (deepCS D.P).Com := inferInstanceAs (Fintype (Fin (2 ^ D.n) → B))
instance (D : DeepRap Φ F B) : DecidableEq (deepCS D.P).Com := inferInstanceAs (DecidableEq (Fin (2 ^ D.n) → B))
instance (D : DeepRap Φ F B) : Inhabited (deepCS D.P).Com := inferInstanceAs (Inhabited (Fin (2 ^ D.n) → B))

/-- **IOP parameters**: the interaction interfaces of the staged statement (no commitment data). -/
structure IopParams (D : DeepRap Φ F B) where
  [dM0 : DecidableEq (D.P.statement D.R0 D.Rest).M0]
  [fM0 : Finite (D.P.statement D.R0 D.Rest).M0]
  [dMf : DecidableEq (deepPlan D.P D.A D.R0 D.Rest D.RestV).Mfin]
  [fMf : Finite (deepPlan D.P D.A D.R0 D.Rest D.RestV).Mfin]
  I0 : OracleInterface (D.P.statement D.R0 D.Rest).M0
  I : (r : ℕ) → OracleInterface (Cols D.P.colRoundX (Fin (2 ^ D.n) → B) r)
  Ifin : OracleInterface (deepPlan D.P D.A D.R0 D.Rest D.RestV).Mfin

namespace IopParams

variable {D : DeepRap Φ F B}

/-- Adversaries: a single-salt adversary of the IOP round list, with its guard schedule. -/
structure IopAdv (pp : IopParams D) where
  Statement : Type
  GlobalSalt : Type
  Witness : Type
  [dSt : DecidableEq Statement]
  [dSa : DecidableEq GlobalSalt]
  guards : GuardSchedule (Statement × GlobalSalt) PUnit
    (letI := pp.dM0; letI := pp.fM0; letI := pp.dMf; letI := pp.fMf
     sRounds (D.P.statement D.R0 D.Rest) (deepCS D.P) (deepPlan D.P D.A D.R0 D.Rest D.RestV) pp.I0 pp.I pp.Ifin D.nb)
  adversary : SingleSaltAdversary Statement GlobalSalt Witness
    (letI := pp.dM0; letI := pp.fM0; letI := pp.dMf; letI := pp.fMf
     sRounds (D.P.statement D.R0 D.Rest) (deepCS D.P) (deepPlan D.P D.A D.R0 D.Rest D.RestV) pp.I0 pp.I pp.Ifin D.nb)

attribute [instance] IopAdv.dSt IopAdv.dSa

variable {pp : IopParams D}

/-- Budget: at most `Q_FS` fresh keys (the other three budgets are unused: no hash, no opened-claims accounting). -/
def Budget (A : IopAdv pp) (Q_FS _Q_H _V _Pn : ℕ) : Prop :=
  ∀ phase ∈ support (randomOracleLoggedRun A.adversary.withQueryLog ∅), (freshKeysOfLog phase.1.2).card ≤ Q_FS

/-- `Pr[accepted ∧ ¬ Holds]` in the single-salt FS game. -/
noncomputable def bad (A : IopAdv pp) : ℝ≥0∞ :=
  letI := pp.dM0; letI := pp.fM0; letI := pp.dMf; letI := pp.fMf
  Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (sRounds (D.P.statement D.R0 D.Rest) (deepCS D.P) (deepPlan D.P D.A D.R0 D.Rest D.RestV) pp.I0 pp.I pp.Ifin D.nb)
        A.guards
        (sAccept (D.P.statement D.R0 D.Rest) (deepCS D.P) (deepPlan D.P D.A D.R0 D.Rest D.RestV) pp.I0 pp.I pp.Ifin D.nb)
        A.adversary) ∅)}[
      (∃ x, joint.1.1.1 = some x) ∧ ¬ D.R0.Holds]

/-- The error: `Q · max_j errs j + Σ_j errs j` (`ε_CS = 0`). -/
noncomputable def eps (pp : IopParams D) (Q_FS _Q_H _V _Pn : ℕ) : ℝ≥0∞ :=
  letI := pp.dM0; letI := pp.fM0; letI := pp.dMf; letI := pp.fMf
  Q_FS * Finset.univ.sup (sErrors (D.P.statement D.R0 D.Rest) (deepCS D.P) (deepPlan D.P D.A D.R0 D.Rest D.RestV)
        pp.I0 pp.I pp.Ifin D.nb (errDeep D.P D.errOld)) +
    ∑ j, sErrors (D.P.statement D.R0 D.Rest) (deepCS D.P) (deepPlan D.P D.A D.R0 D.Rest D.RestV)
        pp.I0 pp.I pp.Ifin D.nb (errDeep D.P D.errOld) j

end IopParams

/-- **`iopPcs`**: honest oracle access (`iopCS`, `ε_CS = 0`). `sound` is `rap_succinct_sound_deep`. -/
noncomputable instance iopPcs : PcsBase Φ F B where
  Params := IopParams
  ParamsOk _ _ := True
  Adv _ pp := IopParams.IopAdv pp
  Budget _ pp A := IopParams.Budget A
  bad _ pp A := IopParams.bad A
  ε _ pp := IopParams.eps pp
  sound D pp _ A Q_FS Q_H V Pn hb := by
    cases pp
    cases A
    unfold IopParams.Budget at hb
    unfold IopParams.bad IopParams.eps
    exact rap_succinct_sound_deep D.P D.R0 D.Rest D.hR0 D.hlink D.hnb (deepPlan D.P D.A D.R0 D.Rest D.RestV)
      (link_deepPlan D.P D.A D.R0 D.Rest D.RestV D.hRest) _ _ _ D.errOld D.herr0 _ _ Q_FS hb

#print axioms NockvmE2E.Succ.Pcs.iopPcs

end NockvmE2E.Succ.Pcs
