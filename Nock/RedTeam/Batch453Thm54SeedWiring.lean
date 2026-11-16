/-
  Nock/RedTeam/Batch453Thm54SeedWiring.lean

  **Verifier seed wired into publics 3..5.**

  Publics `3..5` of the family compute chip are `seedOfClaim`: `αc · RLC^γ(LT_comp of the public claim)`.  N4
  (`ComputeWalkSeed.pub_state_eq_rootStateOfFormula`) plus
  `genComputeSkeleton_root_state` supply the root-state fact; no package
  field was added.

  `computeChipAt_honest_of_chalVal` is the generic honest identity under
  the N4/`root_bindings` hypotheses.  Strategy-typed
  `public_subject/formula/result` still inhabit `strategyOfTraces`, which
  takes `TracesBindsHyps` as a constructor argument — they cannot be
  restated at that type without `hbinds`.  The chip-level seed half is
  definitional.

  Negative: a first-row label whose RLC differs from the claim's, at
  `alphaC ≠ 0` and leaf fanout, makes `walkAccInit` nonzero.
-/
import Nock.NockVMROM.Thm54.ComputeWalkSeed
import Nock.NockVMROM.Thm54.ComputeWalkLabel
import Nock.NockVMROM.Thm54.CoordinateBasis
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.FamilyComputeRows
import Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
import Nock.NockVMROM.Thm54.OpcodeSemantics
import Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
import Nock.NockVMROM.Thm54.TraceGen.GenRootState
import Nock.RedTeam.Batch398Thm54PublicConjuncts
import Nock.RedTeam.Batch403Thm54PublicFromSeedBlocked
import Nock.GlobalCarryRecognizer
import Nock.NockVMROM.Thm54.P8Core.Batch453Thm54SeedWiring
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch453

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam.Batch398
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.Framework
open Module
open MonolithicRAP
open OptimizedComputeHostileAccumulator

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## Seed wiring -/

/-- Off the walk block `0..5` the family map is still the package map. -/
theorem family_off_seed
    (c : OptimizedProductionChallengeTuple K F) (j : ℕ)
    (hj : ¬ j < 6) :
    P.familyComputePublic c j = P.optimized.computePublic j :=
  computePublicOfTuple_eq_pkg_off_seed P.optimized.basis
    P.optimized.verifier.raw.claim P.optimized.computePublic c j hj

/-- N4: no package field.  The root state is a theorem of `Vcomp.SVhead`
    plus `RootRealization` plus `PairFaithful`. -/
def n4_is_a_theorem :=
  @pub_state_eq_rootStateOfFormula

/-- Generator-side root state (`TraceGen/GenRootState.lean`).  `Gen.lean`
    is unedited. -/
theorem generator_root_state
    (fuel : ℕ) (subject formula : Noun)
    (t : Walk.NTree (GenComputeRow K)) (result : Noun)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    t.label.skel.state = rootStateOfFormula formula :=
  genComputeSkeleton_root_state (K := K) fuel subject formula t result h

/-- F73 unfolding lemma — not bare `rfl` on a generated skeleton. -/
theorem f73_root_state :
    rootStateOfFormula (.cell (.atom 1) (.atom 2)) = .s1 :=
  f73_formula_root_state

/-- F97 unfolding lemma. -/
theorem f97_root_state (tl : Noun) :
    rootStateOfFormula (.cell (.atom 5) tl) = .s5 :=
  f97_formula_root_state tl

/-! ## Chip-level public conjuncts -/

/-- They stay off
    the live list.  Chip-close of the *strategy-typed* conjuncts is
    blocked: `strategyOfTraces` takes `TracesBindsHyps` as a constructor
    argument. -/
def publicNames : List String := ["public_subject", "public_formula", "public_result"]

theorem public_names_not_open :
    ∀ name ∈ publicNames, name ∉ openConjuncts := by
  decide

/-- `public_*` were already hypothesis-closed; they are not yet
    chip-closed. -/
def openConjunctsAfterSeed : List String := openConjuncts

theorem openConjunctsAfterSeed_length :
    openConjunctsAfterSeed.length = 10 :=
  openConjuncts_length

/-- Seed half of the chip-level public bind: the family chip's publics
    `3..5` are `seedOfClaim`, from `DeployedAcceptanceAt`'s chip (the
    wiring is in `computeChipAt`, so the acceptance is not consulted). -/
theorem public_conjuncts_from_chip
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (_hAcc : DeployedAcceptanceAt P c Qc Qm) (k : Fin 3) :
    P.familyComputePublic c (3 + (k : ℕ)) =
      coord P.optimized.basis
        (seedOfClaim P.optimized.verifier.raw.claim c) k :=
  family_seed_slots P c k

/-- First-row `walkAccInit` vanishes on every accepted family row
    (`correctedEndpoint4` = `[finalMaskedWalkAccInit]`). -/
theorem walkAccInit_vanishes_from_chip
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (i : Fin (rows P)) :
    ∀ t ∈ correctedEndpoint4, t.eval (rowEnvAt P c Qc i) = 0 :=
  (row_obligations_at P c Qc hsat i).endpointDegreeFour1

/-- Degree-two endpoints (including `finalAccInit` and `finalMaskedWalkLn1`)
    vanish on every accepted family row. -/
theorem endpoint2_vanishes_from_chip
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (i : Fin (rows P)) :
    ∀ t ∈ correctedEndpoint2, t.eval (rowEnvAt P c Qc i) = 0 :=
  (row_obligations_at P c Qc hsat i).endpointDegreeTwo2


/-- Remaining assembly for chip-close of decoded `s`/`f`/`e`: `walkAccInit` eval at row 0 ⇒
    `αc · RLC^γ(firstReader label) = seedOfClaim` (needs `acc(0)=0`,
    `ln(0)=αc`, and the leaf/`cc` identity), `labelRLC_eval` at
    `firstReader`, then `Walk.rlc` injectivity outside the priced
    collision.  No new package field.  `strategyOfTraces` still needs
    `TracesBindsHyps` to inhabit the AcceptedContent type. -/
def CHIP_SFE_REMAINING : List String :=
  ["walkAccInit_eval_at_row0", "labelRLC_eval firstReader",
    "Walk.rlc injectivity", "strategyOfTraces takes TracesBindsHyps"]

theorem chip_sfe_remaining_length : CHIP_SFE_REMAINING.length = 4 := by decide

/-- Chip-closed publics stay 0. -/
theorem chip_closed_publics_still_zero :
    Batch403.chipClosedPublics = 0 :=
  rfl

/-! ## Negative — mismatched first-row label vs claim seed -/

/-- Functional rejection at `walkAccInit`.  Coin condition: `alphaC ≠ 0`.  On a leaf first row
    (`cc = 0`, `acc = 0`, `ln = αc`) a label RLC other than the claim's
    makes the init gate nonzero, so the family chip rejects. -/
theorem mismatched_root_label_walkAccInit_nonzero
    (αc seed cur acc cc : K) (hα : αc ≠ 0)
    (hacc : acc = 0) (hcc : cc = 0)
    (hcur : cur ≠ seed / αc) :
    αc * cur + acc - (αc * cc + seed) ≠ 0 := by
  subst hacc hcc
  simp only [mul_zero, add_zero, zero_add]
  intro h
  have : cur * αc = seed := by
    simpa [mul_comm] using sub_eq_zero.mp h
  have hdiv : cur = seed / αc := (eq_div_iff_mul_eq hα).mpr this
  exact hcur hdiv

/-- Coin condition named: `alphaC c.1 ≠ 0`.  `γ` injectivity of `rlc`
    is the priced walk collision, not an extra package field. -/
def rejectionCoinCondition : String := "alphaC c.1 ≠ 0"

end

end Nock.RedTeam.Batch453

#print axioms Nock.RedTeam.Batch453.family_seed_slots
#print axioms Nock.RedTeam.Batch453.n4_is_a_theorem
#print axioms Nock.RedTeam.Batch453.generator_root_state
#print axioms Nock.RedTeam.Batch453.public_conjuncts_from_chip
#print axioms Nock.RedTeam.Batch453.walkAccInit_vanishes_from_chip
#print axioms Nock.RedTeam.Batch453.mismatched_root_label_walkAccInit_nonzero
