/-
the RAP -> claims step as a class.

* `RapCompiler R CS nb`: a compiler from the RAP statement `R` to opening claims on the commitment scheme `CS`:
  the claims it produces and checks (`plan`), the link "true openings + check ⇒ the full verifier accepts"
  (`link`), the RAP-level certificate, and the per-round errors (`err`, the compiler's error budget `ε_comp`).
  `epsComp` is its error `Q · max_j errs j + Σ_j errs j` ("claims hold ⇒ RAP holds, except ε_comp").
* `e2e_of_compiler_pcs`: for ANY compiler and ANY commitment scheme with extraction-failure bound `ε_PCS`,
  `Pr[accepted ∧ ¬Holds] ≤ ε_comp + ε_PCS` (a repackaging of `rap_succinct_sound`).
* `deepCompiler`: DEEP-ALI as the instance (`deepPlan`, `link_deepPlan`, `certificate_deep`, `errDeep`).
* `deep_iop_recovers`: the J-8 compiler with the IOP scheme recovers `rap_succinct_sound_deep`'s bound.

BLOCKER: the (DEEP, FRI+Merkle) choice recovering
`rap_fri_merkle_sound_deep` needs an extractability bound `ε_PCS` for FRI+Merkle; none exists (the theorem is a
compiled-soundness statement). The FRI+Merkle side is therefore `friMerklePcs`.
-/
import NockvmE2E.Succ.PcsBase
import NockvmE2E.Succ.PcsIop

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

section Generic

variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} {O : OracleInterface β}
  [SampleableType K] [Inhabited K] [Fintype ι] [DecidableEq ι]

/-- **A RAP -> claims compiler** into the commitment scheme `CS` (`nb` sampled rounds). -/
structure RapCompiler (R : RapStatement Φ K ι β colRound) (CS : CommitScheme β O) (nb : ℕ) where
  /-- the claims produced, their proof and the residual check -/
  plan : OpenPlan R CS
  /-- true openings and the check make the full verifier accept -/
  link : Link R CS plan
  /-- the RAP-level certificate -/
  cert : Certificate R blkOf nb
  /-- the per-round error budget (`ε_comp`: the RAP's own rounds plus the compiler's extra challenges) -/
  err : ℕ → ℝ≥0∞
  herr : ∀ m0 r, roundBound R blkOf m0 r ≤ err r

variable {R : RapStatement Φ K ι β colRound} {CS : CommitScheme β O} {nb : ℕ}
  [Fintype CS.Com] [DecidableEq CS.Com] [Inhabited CS.Com]
  [DecidableEq R.M0] [Finite R.M0]

/-- **The compiler's error** `ε_comp(Q) = Q · max_j errs j + Σ_j errs j`. -/
noncomputable def RapCompiler.epsComp (C : RapCompiler R CS nb) [DecidableEq C.plan.Mfin] [Finite C.plan.Mfin]
    (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound CS.Com r))
    (Ifin : OracleInterface C.plan.Mfin) (Q : ℕ) : ℝ≥0∞ :=
  Q * Finset.univ.sup (sErrors R CS C.plan I0 I Ifin nb C.err) + ∑ j, sErrors R CS C.plan I0 I Ifin nb C.err j

/-- **`e2e_of_compiler_pcs`: ε ≤ ε_comp + ε_PCS.** For every compiler `C` and every commitment scheme whose
extraction fails with probability at most `ε_PCS`, the accepted-and-false probability is at most the sum. -/
theorem e2e_of_compiler_pcs (C : RapCompiler R CS nb) [DecidableEq C.plan.Mfin] [Finite C.plan.Mfin]
    (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound CS.Com r))
    (Ifin : OracleInterface C.plan.Mfin)
    {Statement GlobalSalt Witness : Type} [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R CS C.plan I0 I Ifin nb))
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness (sRounds R CS C.plan I0 I Ifin nb))
    (Q : ℕ) (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q)
    (εPCS : ℝ≥0∞)
    (hCS : Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (sRounds R CS C.plan I0 I Ifin nb) guards (sAccept R CS C.plan I0 I Ifin nb) adversary) ∅)}[
        ∃ z p w, joint.1.1.1 = some (z, p, w) ∧ ExtFailAt R CS C.plan I0 I Ifin nb p] ≤ εPCS) :
    Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (sRounds R CS C.plan I0 I Ifin nb) guards (sAccept R CS C.plan I0 I Ifin nb) adversary) ∅)}[
        (∃ x, joint.1.1.1 = some x) ∧ ¬ R.Holds] ≤ C.epsComp I0 I Ifin Q + εPCS :=
  rap_succinct_sound C.cert C.link C.err C.herr guards adversary Q queryBound εPCS hCS

/-- With a perfectly extractable scheme (`ε_PCS = 0`) the error is `ε_comp` alone. -/
theorem e2e_of_compiler_perfect (hP : CS.PerfectlyExtractable)
    (C : RapCompiler R CS nb) [DecidableEq C.plan.Mfin] [Finite C.plan.Mfin]
    (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound CS.Com r))
    (Ifin : OracleInterface C.plan.Mfin)
    {Statement GlobalSalt Witness : Type} [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R CS C.plan I0 I Ifin nb))
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness (sRounds R CS C.plan I0 I Ifin nb))
    (Q : ℕ) (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (sRounds R CS C.plan I0 I Ifin nb) guards (sAccept R CS C.plan I0 I Ifin nb) adversary) ∅)}[
        (∃ x, joint.1.1.1 = some x) ∧ ¬ R.Holds] ≤ C.epsComp I0 I Ifin Q :=
  rap_succinct_sound_perfect hP C.cert C.link C.err C.herr guards adversary Q queryBound

end Generic

section Deep

variable {Φ : CoinFrame} {F B : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
  [Field B] [Fintype B] [DecidableEq B] [Algebra B F] [Inhabited B] [SampleableType F] [Inhabited F]

/-- **DEEP-ALI as a `RapCompiler`**: the DEEP opening plan (`deepPlan`), its link (`link_deepPlan`), the
certificate of the DEEP-extended RAP (`certificate_deep`), errors `errDeep` (`ε_α` at `R`, `ε_ζ` at `R+1`). -/
noncomputable def deepCompiler (D : DeepRap Φ F B) :
    RapCompiler (D.P.statement D.R0 D.Rest) (deepCS D.P) D.nb where
  plan := deepPlan D.P D.A D.R0 D.Rest D.RestV
  link := link_deepPlan D.P D.A D.R0 D.Rest D.RestV D.hRest
  cert := certificate_deep D.P D.R0 D.Rest D.hlink blkOf D.nb (certificate_of_input D.hR0) D.hnb blkOf
    (fun _ _ _ => rfl) (blkOf_sAlpha D.P) (blkOf_sZeta D.P)
  err := errDeep D.P D.errOld
  herr m0 r := by
    refine (roundBound_deep D.P D.R0 D.Rest m0 r).le.trans ?_
    unfold errDeep
    gcongr
    exact D.herr0 m0 r

/-- The IOP instance's error is the DEEP compiler's error `ε_comp` (`ε_PCS = 0`). -/
theorem iopEps_eq_epsComp (D : DeepRap Φ F B) (pp : IopParams D) (Q_FS Q_H V Pn : ℕ) :
    IopParams.eps pp Q_FS Q_H V Pn =
      letI := pp.dM0; letI := pp.fM0; letI := pp.dMf; letI := pp.fMf
      letI : DecidableEq (deepCompiler D).plan.Mfin := pp.dMf
      letI : Finite (deepCompiler D).plan.Mfin := pp.fMf
      (deepCompiler D).epsComp pp.I0 pp.I pp.Ifin Q_FS := rfl

/-- **The J-8 compiler (DEEP-ALI) with the IOP scheme recovers `rap_succinct_sound_deep`'s bound**, now as an
instance of the generic `e2e_of_compiler_perfect` (`iopCS` is perfectly extractable, `ε_PCS = 0`). -/
theorem deep_iop_recovers (D : DeepRap Φ F B) (pp : IopParams D) (A : IopParams.IopAdv pp) (Q_FS : ℕ)
    (hb : IopParams.Budget A Q_FS 0 0 0) :
    IopParams.bad A ≤ IopParams.eps pp Q_FS 0 0 0 := by
  letI := pp.dM0; letI := pp.fM0; letI := pp.dMf; letI := pp.fMf
  letI : DecidableEq (deepCompiler D).plan.Mfin := pp.dMf
  letI : Finite (deepCompiler D).plan.Mfin := pp.fMf
  exact e2e_of_compiler_perfect (iopCS_perfect _) (deepCompiler D) pp.I0 pp.I pp.Ifin A.guards A.adversary Q_FS hb

end Deep

end NockvmE2E.Succ.Pcs

#print axioms NockvmE2E.Succ.Pcs.e2e_of_compiler_pcs
#print axioms NockvmE2E.Succ.Pcs.e2e_of_compiler_perfect
#print axioms NockvmE2E.Succ.Pcs.deepCompiler
#print axioms NockvmE2E.Succ.Pcs.iopEps_eq_epsComp
#print axioms NockvmE2E.Succ.Pcs.deep_iop_recovers
