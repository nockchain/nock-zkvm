/-
  Nock/RedTeam/Batch259Thm54GenuineEvalNBroadProgram.lean

  **Non-vacuity for the `evalFBy q` → `Nock.evalN` soundness upgrade.**

  `Thm54/GenuineEvalN.lean` upgrades what an accepted, non-failing proof certifies from the
  paper's modular evaluator `FieldEmbedding.evalFBy q` (OP_4 = `(1+n) mod p`, the paper)
  to `Nock.evalN`, under three side conditions on the *committed public nouns*:

  * `FieldEmbedding.BoundedBy q subject`, `FieldEmbedding.BoundedBy q formula` — the paper's own
    typing of a Nock program (the paper; Def[Nock Program] item 1, the paper:
    `subject, formula ∈ 𝒩^λ(𝔽)`), and
  * `GenuineEvalN.NoOverflowRun q subject formula` — the guarded evaluator `evalGBy q`, which
    crashes rather than wrapping, terminates.

  This file discharges all three at `q = 769` for `GenBroadProgram.bpTree`, the seventeen-row,
  eight-state generated program of `Batch231`/`Batch232`/`Batch256`/`Batch257`, and then *runs the
  upgrade on the soundness path*: the `Nock.evalN` conclusion in
  `b259_evalN_of_accepted_at_broad_program` is obtained from
  `Batch257.b257_genuineTarget_at_broad_program`'s accepting coin through
  `GenuineEvalN.holds_of_genuineTargetAt`, not from `genComputeSkeleton_evalN`.

  Scope: the discharge of the three side conditions is a claim about **this** program at **this**
  carrier (`K = GaloisField 769 3`, `Λ = 22`, `q = 769`).  The upgrade theorems in
  `Thm54/GenuineEvalN.lean` are generic; only their instantiation here is fixture-scoped.
-/
import Nock.NockVMROM.Thm54.GenuineEvalN
import Nock.NockVMROM.Thm54.BuildableAxisWitness
import Nock.RedTeam.Batch231Thm54BroadProgramSemanticData
import Nock.RedTeam.Batch232Thm54BroadProgramData
import Nock.RedTeam.Batch256Thm54InputsAtBroadProgram
import Nock.RedTeam.Batch257Thm54GenuineTargetAtBroadProgram
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 40000

namespace Nock.RedTeam.Batch259

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam
open Nock.RedTeam.Batch231
open Nock.RedTeam.Batch232

abbrev DK := DotConfig769.K
abbrev DF := DotConfig769.F

local instance charRingDK : CharP DK (ringChar DK) := ringChar.charP DK

noncomputable section



variable (hax : FormRAxisBound Batch256.bpPackage.optimized.sampled
    Batch256.bpPackage.optimized.basis)
variable (hbasis : FormRBasis Batch256.bpPackage.optimized.basis)
variable (hwidth : FormRWidth DF)
include hax hbasis hwidth

/-! ## 1. The three side conditions, at the broad program and `q = 769` -/

omit hax hbasis hwidth in
/-- The committed subject `[5 7]` is a field noun at `q = 769`. -/
theorem b259_subject_bounded : FieldEmbedding.BoundedBy 769 bpSubject := by
  simp [FieldEmbedding.BoundedBy, bpSubject]

omit hax hbasis hwidth in
/-- The committed formula is a field noun at `q = 769`. -/
theorem b259_formula_bounded : FieldEmbedding.BoundedBy 769 bpFormula := by
  simp [FieldEmbedding.BoundedBy, bpFormula, bpR1, bpR2, bpR3,
    bp7, bp7Tail, bp7B, bp7C, bp8, bp8Tail, bp8B, bp8C,
    bp5, bp5Tail, bp5B, bp5C, bp4, bp4Tail, bp3, bp3Tail, bp3Call]

omit hax hbasis hwidth in
/-- **The guarded run terminates**: evaluating `bpFormula` against `bpSubject` performs no modular
reduction at `769`.  Six fuel suffice. -/
theorem b259_guarded_run :
    FieldEmbedding.evalGBy 769 6 bpSubject bpFormula = some bpResult := by
  simp [FieldEmbedding.evalGBy, FieldEmbedding.lusGBy,
    bpSubject, bpFormula, bpR1, bpR2, bpR3,
    bp7, bp7Tail, bp7B, bp7C, bp8, bp8Tail, bp8B, bp8C,
    bp5, bp5Tail, bp5B, bp5C, bp4, bp4Tail, bp3, bp3Tail, bp3Call,
    bpResult, bpR1Result, bpR2Result, bpR3Result, Noun.slot, Noun.wut, Noun.tis]

omit hax hbasis hwidth in
/-- The no-overflow side condition of `GenuineEvalN`, discharged. -/
theorem b259_noOverflow : GenuineEvalN.NoOverflowRun 769 bpSubject bpFormula :=
  GenuineEvalN.noOverflowRun_of_guarded b259_guarded_run

/-! ## 2. The bridge fires at the committed claim, with no free hypotheses

`b259_field_run` is computed independently of `b259_guarded_run`, so `b259_bridge_concrete` really
does combine a *modular* conclusion with the no-overflow condition rather than restating one fact
twice.  The claim triple is `⟨bpSubject, bpFormula, bpResult⟩` (`Batch256.b256_claim_triple`). -/

omit hax hbasis hwidth in
/-- The paper's modular evaluator on the same program (OP_4 reduces mod `769`). -/
theorem b259_field_run :
    FieldEmbedding.evalFBy 769 6 bpSubject bpFormula = some bpResult := by
  simp [FieldEmbedding.evalFBy, FieldEmbedding.lusFBy,
    bpSubject, bpFormula, bpR1, bpR2, bpR3,
    bp7, bp7Tail, bp7B, bp7C, bp8, bp8Tail, bp8B, bp8C,
    bp5, bp5Tail, bp5B, bp5C, bp4, bp4Tail, bp3, bp3Tail, bp3Call,
    bpResult, bpR1Result, bpR2Result, bpR3Result, Noun.slot, Noun.wut, Noun.tis]

omit hax hbasis hwidth in
/-- The modular claim of the broad program: exactly the content of `GenuineWitness`'s
`publicClaimHoldsMod` field at this claim triple. -/
theorem b259_holdsMod :
    (⟨bpSubject, bpFormula, bpResult⟩ : P8PublicClaim).HoldsMod 769 :=
  ⟨6, b259_field_run⟩

omit hax hbasis hwidth in
/-- **The bridge at a concrete program, with no free hypotheses**: the modular conclusion plus the
three side conditions gives the `Nock.evalN` conclusion. -/
theorem b259_bridge_concrete :
    (⟨bpSubject, bpFormula, bpResult⟩ : P8PublicClaim).Holds :=
  GenuineEvalN.holds_of_holdsMod (by norm_num) _
    b259_subject_bounded b259_formula_bounded b259_noOverflow b259_holdsMod

/-! ## 3. The soundness path: accepted ⟹ genuine `Nock.evalN` conclusion

The `Nock.evalN` conjunct below is produced by `GenuineEvalN.holds_of_genuineTargetAt` applied to
`Batch257`'s accepting coin, i.e. from *acceptance*, and never from `genComputeSkeleton_evalN`. -/

/-- **Non-vacuity headline.**  There is a released package at `GenBroadProgram.bpTree` whose
committed claim is `⟨bpSubject, bpFormula, bpResult⟩` and an accepting coin outside the five-class
failure union, such that the `GenuineEvalN` upgrade fires and certifies the claim against the
**real** Nock evaluator `Nock.evalN` — not the modular `evalFBy 769`. -/
theorem b259_evalN_of_accepted_at_broad_program :
    ∃ package : OptimizedFullStrictNockVMROMPackage DF DK 8,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim =
            ⟨bpSubject, bpFormula, bpResult⟩
        ∧ ∃ ω : JointCoins DK,
            package.strategy.Accepts ω Batch231.bpChal.lam ∧
              ω ∉ ProductionP8Containment.FailureUnion package.strategy
                    package.optimized.census Batch231.bpChal.lam ∧
              GenuineTargetAt package.strategy 769 22 ω Batch231.bpChal.lam ∧
              (∃ fuel : ℕ, Nock.evalN fuel bpSubject bpFormula = some bpResult) := by
  obtain ⟨package, hstmt, hclaim, -, ω, hacc, hout, hgen⟩ :=
    Batch257.b257_genuineTarget_at_broad_program hax hbasis hwidth
  have hclaim' : package.strategy.verifier.raw.claim =
      ⟨bpSubject, bpFormula, bpResult⟩ := hclaim
  have hs : FieldEmbedding.BoundedBy 769 package.strategy.verifier.raw.claim.subject := by
    rw [hclaim']; exact b259_subject_bounded
  have hf : FieldEmbedding.BoundedBy 769 package.strategy.verifier.raw.claim.formula := by
    rw [hclaim']; exact b259_formula_bounded
  have hno : GenuineEvalN.NoOverflowRun 769 package.strategy.verifier.raw.claim.subject
      package.strategy.verifier.raw.claim.formula := by
    rw [hclaim']; exact b259_noOverflow
  have hholds : package.strategy.verifier.raw.claim.Holds :=
    GenuineEvalN.holds_of_genuineTargetAt hgen (by norm_num) hs hf hno
  rw [hclaim'] at hholds
  exact ⟨package, hstmt, hclaim, ω, hacc, hout, hgen, hholds⟩

end

end Nock.RedTeam.Batch259

#print axioms Nock.RedTeam.Batch259.b259_guarded_run
#print axioms Nock.RedTeam.Batch259.b259_noOverflow
#print axioms Nock.RedTeam.Batch259.b259_bridge_concrete
#print axioms Nock.RedTeam.Batch259.b259_evalN_of_accepted_at_broad_program
