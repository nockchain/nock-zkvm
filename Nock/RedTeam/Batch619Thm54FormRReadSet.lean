/-
  Nock/RedTeam/Batch619Thm54FormRReadSet.lean

  A4, the load-bearing receipt: the Form R axis event's
  bad set reads only coordinates sampled before the `(α, λ)` round, with the read set stated
  against the landed encode `MemoryRowTemplate.specialize α lmb = encodeRow lmb ∘ specializeA α`.

  Symbol by symbol, the bad set `FormRAxisEvent.formRBadAt E i E' x` reads:
  * the template tree's shape and record exponents (`templateAxisTree (templateMemoryTreeAt E i)`);
  * the certificate of each read-root row through `preEncode (x αM) (x λ) = specializeA (x αM)`,
    i.e. the argument of `encodeRow (x λ)` — `nockAxisOf` of its axis field, which `specializeA`
    leaves as the template's (`certAxisAt_active`, `certAxisVia_preEncode`);
  * nothing of the encode's OUTPUT.
  Result: `formRBadAt_readsOn` (prior set `{z, a, b, c}`) and the sharper `ReadsOn ∅`.

  **Positive controls.**  (1) the same row read through the encode's output — the executed
  `T = λ^m` — fails `ReadsOn` (`encodedTBad_not_readsOn`, at an active row with axis `2`);
  (2) a set reading the landed `λ` coordinate fails (`lambdaBad_not_readsOn`).

  **No second λ.**  The `λ` here is `landedVec c 10 = c.2.2.2.lambda`, which is memory slot `8`
  and compute slot `9`; the template has no `λ` and `specialize` writes `ChallengeVector.lam`.
-/
import Nock.NockVMROM.Thm54.FormRAxisEvent

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch619

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.FormRAxisEvent
open SemanticTimestampStrategy

section A4

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

/-- The read set is stated against the landed encode. -/
theorem readSet_against_landed_encode (α lmb : K) (row : MemoryRowTemplate (K := K)) :
    row.specialize α lmb = MemoryRowTemplate.encodeRow lmb (preEncode α lmb row) ∧
      preEncode α lmb row = row.specializeA α :=
  ⟨specialize_eq_encode_preEncode α lmb row, rfl⟩

/-- **A4.** -/
theorem a4_readsOn {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (i : Fin T.kMem)
    (Edeg : ℕ) :
    ReadsOn (C := K) (n := 11) (priorCoords landedRound lamIdx) (formRBadAt E i Edeg) ∧
      priorCoords landedRound lamIdx = ({3, 6, 7, 8} : Finset (Fin 11)) ∧
      lamIdx ∉ priorCoords landedRound lamIdx ∧ alphaMIdx ∉ priorCoords landedRound lamIdx :=
  ⟨formRBadAt_readsOn E i Edeg, lambda_prior, lam_not_prior, alphaM_not_prior⟩

/-- A4, sharper: a template quantity. -/
theorem a4_readsOn_empty {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (i : Fin T.kMem) (Edeg : ℕ) :
    ReadsOn (C := K) (n := 11) (∅ : Finset (Fin 11)) (formRBadAt E i Edeg) :=
  formRBadAt_readsOn_empty E i Edeg

/-- Positive control (1): reading the encode's output `T` fails. -/
theorem a4_positive_control_encoded (row : MemoryRowTemplate (K := K))
    (ha : memoryMemRecKind row.timestamp.state = .active)
    (hax : row.placeholder.2.2.mem.axis = ((2 : ℕ) : K)) (h2 : 2 < ringChar K) :
    ¬ ReadsOn (C := K) (n := 11) (priorCoords landedRound lamIdx) (encodedTBad row) :=
  encodedTBad_not_readsOn row ha hax h2

/-- Positive control (2): reading the landed `λ` coordinate fails. -/
theorem a4_positive_control_lambda :
    ¬ ReadsOn (C := K) (n := 11) (priorCoords landedRound lamIdx)
      (fun x : Fin 11 → K => ({x lamIdx} : Finset K)) :=
  lambdaBad_not_readsOn

/-- The certificate the event reads is the one the landed encode evaluates at `λ`. -/
theorem certificate_is_landed (α lmb : K) (row : MemoryRowTemplate (K := K))
    (ha : memoryMemRecKind row.timestamp.state = .active) :
    (row.specialize α lmb).2.2.mem.axis =
        (Batch575.Tpoly (K := K) (MemoryTable.formRCertShift (templateRowCertAxis row))).eval lmb ∧
      (row.specialize α lmb).2.2.cprime =
        (Batch575.C'poly (K := K) (formRN K)
          (certBitsOf (fun _ => templateRowCertAxis row) 0)).eval lmb :=
  ⟨encode_T_eq_Tpoly_eval α lmb row ha, encode_Cprime_eq_C'poly_eval α lmb row ha⟩

end A4

/-- No second λ: the event's λ is the landed tuple's, read by both chips. -/
theorem no_second_lambda {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [Fintype F]
    [DecidableEq K] [FiniteDimensional F K] (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (T : ExactConfigTemplate F K) (α lmb : K) :
    (landedVec c lamIdx = c.2.2.2.lambda ∧
      DeployedChipFamily.memoryKOfTuple c 8 = c.2.2.2.lambda ∧
      DeployedChipFamily.computeKOfTuple c 9 = c.2.2.2.lambda) ∧
    (T.specialize α lmb).challenges.lam = lmb ∧
    Fintype.card (OptimizedStrictPackage.OptimizedProductionChallengeTuple K F) =
      Fintype.card K ^ 11 :=
  ⟨landedVec_lambda c, template_lam_is_sampled T α lmb, landed_card K F⟩

end Nock.RedTeam.Batch619

#print axioms Nock.RedTeam.Batch619.a4_readsOn
#print axioms Nock.RedTeam.Batch619.a4_positive_control_encoded
#print axioms Nock.RedTeam.Batch619.a4_positive_control_lambda
#print axioms Nock.RedTeam.Batch619.certificate_is_landed
#print axioms Nock.RedTeam.Batch619.no_second_lambda
