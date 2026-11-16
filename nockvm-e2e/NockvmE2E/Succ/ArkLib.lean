/-
SUCC-0, the ArkLib side of the commitment slot (it uses ArkLib's `Commitment.Scheme`).

* `evalOI toPoly`: the univariate EVALUATION oracle on a column (query = point, response = value), in
  the style of ArkLib's Hachi `multilinearEvalOracleInterface`. With it, `SatClaims` is "the column's
  polynomial takes the claimed values".
* `ArkCommitment`: a typeclass wrapping ArkLib's functional commitment `Commitment.Scheme`
  (`Commitments/Functional/Basic.lean`) together with a straight-line extractor and its
  `extractabilityExperiment` bound `εext` (i.e. a witness of `Commitment.extractability`, :252).
  A lattice scheme (Hachi/Akita) or FRI/Merkle is an instance of THIS class.
* `sat_single_iff`: ArkLib's extractability failure condition `O.answer d q ≠ r` is exactly our
  `¬ SatClaims` on one claim.

What does NOT fit, i.e. why `rap_succinct_sound` takes the thin slot `CommitScheme` and the bound `hCS` in
the composed experiment, not `ArkCommitment.εext` directly:
1. ArkLib's opening is an interactive legacy `Proof` over `ProtocolSpec n` with its own challenge oracle
   `[pSpec.Challenge]ₒ`; in the succinct argument it must run INSIDE the single-salt Fiat–Shamir
   transcript (QD `List Round`), i.e. its rounds appended to `sRounds`. Not built.
2. ArkLib's `extractability` is a STANDALONE game (own keygen, one commitment, adversary then prover);
   transferring `εext` into the composed state-restoration experiment (many commitments, coins hashed
   from them, the adversary grinding) is the CGKY25-type composition theorem. Not proved: that is the gap
   between `εext` and our `hCS`.
3. Single query per game (ArkLib: "TODO multi-instance"); our openings are batched over columns and
   points (`Claims`). `functionBinding` has `Fin L` queries but no extractor.
4. The extractor reads the commit-phase `QueryLog` (`StraightlineExtractor = Commitment → QueryLog → Data`);
   our `ext` reads the commitment only. For Merkle in the ROM the log is essential.
5. `commit` is an `OracleComp` with a `Decommitment`; our slot's honest `commit` is pure.
-/
import NockvmE2E.Succ.Commitment
import ArkLib.Commitments.Functional.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial OracleSpec OracleComp ProtocolSpec
open scoped NNReal ENNReal

namespace NockvmE2E.Succ

/-- The univariate evaluation oracle on a column `b : β` read as `toPoly b`. -/
@[instance_reducible] def evalOI {K β : Type} [Semiring K] (toPoly : β → K[X]) : OracleInterface β where
  Query := K
  toOC :=
    { spec := K →ₒ K
      impl := fun x => do return eval x (toPoly (← read)) }

theorem ans_evalOI {K β : Type} [Semiring K] (toPoly : β → K[X]) (b : β) (x : K) :
    ans (evalOI toPoly) b x = eval x (toPoly b) := rfl

/-- ArkLib's extractability failure condition on ONE claim is our `¬ SatClaims` on the singleton. -/
theorem sat_single_iff {β : Type} (O : OracleInterface β) (d : β) (q : O.Query)
    (r : @OracleInterface.Response β O q) :
    SatClaims O (fun _ : Unit => d) [((), ⟨q, r⟩)] ↔ @OracleInterface.answer β O d q = r := by
  simp [SatClaims, ans]

section Ark

variable {ιo : Type} [DecidableEq ιo] (oSpec : OracleSpec ιo) [∀ t, Fintype (oSpec.Range t)]
  (β : Type) [O : OracleInterface β] (Cm Decommitment ComKey VerifKey : Type)
  {n : ℕ} (pSpec : ProtocolSpec n) [∀ t, Inhabited ([pSpec.Challenge]ₒ.Range t)]
  [∀ t, Fintype ([pSpec.Challenge]ₒ.Range t)] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **ArkLib's functional commitment with its extractability error**, as a typeclass: the scheme, a
straight-line extractor, and the bound `εext` on ArkLib's `extractabilityExperiment` for every
adversary and malicious opening prover. -/
class ArkCommitment where
  scheme : Commitment.Scheme oSpec β Cm Decommitment ComKey VerifKey pSpec
  εext : ℝ≥0
  extractor : Commitment.StraightlineExtractor oSpec β Cm
  extractable : ∀ (AuxState : Type)
    (adversary : Commitment.ExtractabilityAdversary oSpec β Cm AuxState ComKey)
    (prover : Prover oSpec (Cm × (q : O.Query) × O.Response q) AuxState Bool Unit pSpec),
    Commitment.extractabilityExperiment init impl scheme extractor AuxState adversary prover ≤ εext

variable {oSpec β Cm Decommitment ComKey VerifKey pSpec init impl}

/-- An `ArkCommitment` instance is a witness of ArkLib's `Commitment.extractability` at `εext`. -/
theorem ArkCommitment.extractability
    [A : ArkCommitment oSpec β Cm Decommitment ComKey VerifKey pSpec init impl] :
    Commitment.extractability init impl A.scheme A.εext :=
  ⟨A.extractor, A.extractable⟩

end Ark

end NockvmE2E.Succ
