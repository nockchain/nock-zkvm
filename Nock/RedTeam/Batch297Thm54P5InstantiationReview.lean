/-
  Nock/RedTeam/Batch297Thm54P5InstantiationReview.lean

  Paper re-read at source: `:1090-1099`, `:1097`, `:1130-1150`, `:1160`,
  `:1450`.

  No production file under `Nock/NockVMROM/` is edited. Top-level `redteam-status.json` `status` is not flipped.
-/
import Lean
import Nock.Field
import Nock.NockVMROM.Thm54.JointSoundness
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.NockVMROM.Thm54.TraceGen.GenCoinCounting
import Nock.NockVMROM.Thm54.TraceGen.GenGuardedRom
import Nock.NockVMROM.Thm54.TraceGen.GenMatmul
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulConfigGoldilocks
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksHbad
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksResiduals
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulTraceConfined
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.RedTeam.Batch296Thm54P5NockCompiles
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open Lean Elab Command Meta

-- Namespace them; theorems unchanged.
namespace Batch297BinderWalk

def binderTelescope (n : Name) : MetaM (Array (Name × BinderInfo)) := do
  let env ← getEnv
  let some info := env.find? n | throwError m!"missing {n}"
  forallTelescope info.type fun xs _ => do
    xs.mapM fun x => do
      let id := x.fvarId!
      pure (← id.getUserName, ← id.getBinderInfo)

def binderCounts (n : Name) : MetaM (Nat × Nat × Nat) := do
  let tel ← binderTelescope n
  let mut expl := 0
  let mut impl := 0
  let mut inst := 0
  for (_, bi) in tel do
    match bi with
    | .default => expl := expl + 1
    | .implicit | .strictImplicit => impl := impl + 1
    | .instImplicit => inst := inst + 1
  return (tel.size, expl, inst)

def explicitNames (n : Name) : MetaM (Array Name) := do
  let tel ← binderTelescope n
  return tel.filterMap fun (nm, bi) =>
    if bi == .default then some nm else none

run_cmd do
  let n296 : Name := ``Nock.RedTeam.Batch296.b296_nockCompiles_literal
  let n62 : Name := ``Nock.NockVMROM.Thm54.TraceGen.nockCompiles_of_grom_atTree_p62
  let n64 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p64
  let (t296, e296, _) ← liftTermElabM (binderCounts n296)
  if e296 ≠ 5 then
    throwError m!"b296 explicit binders: got {e296}, expected 5 (leftover hfirst/hmore/hax/hbasis/hwidth)"
  logInfo m!"BINDER-COUNT {n296} total={t296} explicit={e296}"
  let e296n ← liftTermElabM (explicitNames n296)
  let e62 ← liftTermElabM (explicitNames n62)
  let e64 ← liftTermElabM (explicitNames n64)
  let residual : Array Name := #[`hcoins, `hbad, `hconf, `haxis, `hgrom]
  for nm in residual do
    if e296n.contains nm then
      throwError m!"b296 still has public residual {nm}"
  for nm in #[`hcoins, `hbad, `hconf] do
    unless e62.contains nm do
      throwError m!"p62 missing expected supplier {nm}"
  if e62.contains `haxis then
    throwError m!"p62 still has haxis (should have been discharged)"
  unless e64.contains `hgrom do
    throwError m!"p64 missing hgrom (still the ∀-program form)"
  if e296n == e64 then
    throwError m!"b296 telescope equals nockCompiles_p64"
  logInfo m!"BINDER-DIFF b296 closed; p62 keeps hcoins/hbad/hconf; no haxis; not p64"

end Batch297BinderWalk

namespace Nock.RedTeam.Batch297

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks
open Nock.RedTeam.Batch296
open Nock.Framework.Thm54

abbrev GF := MatmulConfigGoldilocks.F
abbrev GK := MatmulConfigGoldilocks.K

local instance charRingGK : CharP GK (ringChar GK) := ringChar.charP GK

noncomputable local instance : Fintype GK := Fintype.ofFinite _
noncomputable local instance : DecidableEq GK := Classical.decEq _

noncomputable section

/-! ## F-1. Non-vacuity: claim is this program's `evalN` result. -/

/-- Config abbreviations are the paper Goldilocks carrier. -/
theorem b297_gf : GF = Nock.Field.Fp := rfl

theorem b297_gk : GK = Nock.Field.K := rfl

/-- The claimed noun is the matrix product, not an existentially hidden result. -/
theorem b297_claimed_is_mmC : mmC =
    .cell (.cell (.atom 2) (.atom 1)) (.cell (.atom 1) (.atom 1)) :=
  b296_claimed_is_mmC

/-- `hgrom` is §1's `hrun` -/
theorem b297_grom_implies_evalN {q fuel : ℕ} {subject formula result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result) :
    Nock.evalN fuel subject formula = some result :=
  evalGRom_evalN hgrom

theorem b297_evalN : Nock.evalN 64 mmSubject mmFormula = some mmC :=
  b296_evalN

/-- `P8PublicClaim.Holds` (`JointSoundness.lean`) is the paper evaluator predicate. -/
theorem b297_claim_Holds : P8PublicClaim.Holds ⟨mmSubject, mmFormula, mmC⟩ :=
  ⟨64, b296_evalN⟩

/-- The instance is the Thm 5.4 package **and** the evaluator triple.
    `raw.claim = ⟨subject, formula, result⟩` is the in-tree `claimedResult = result`. -/
noncomputable def b297_instance_nonvacuous :=
  fun hfirst hmore hax hbasis hwidth =>
    (⟨Exists.imp (fun _ hp => ⟨hp.1, hp.2.1⟩) (b296_nockCompiles_literal hfirst hmore hax hbasis hwidth),
      b296_evalN, b297_claim_Holds⟩ :
      (∃ package : OptimizedFullStrictNockVMROMPackage GF GK 16,
        OptimizedFullStrictThm54Statement package
          ∧ package.optimized.verifier.raw.claim =
            ⟨mmSubject, mmFormula, mmC⟩)
      ∧ Nock.evalN 64 mmSubject mmFormula = some mmC
      ∧ P8PublicClaim.Holds ⟨mmSubject, mmFormula, mmC⟩)

/-- A package satisfying the conjunct has `claim.result = mmC`. -/
theorem b297_claim_projects_result
    {P : OptimizedFullStrictNockVMROMPackage GF GK 16}
    (h : P.optimized.verifier.raw.claim = ⟨mmSubject, mmFormula, mmC⟩) :
    P.optimized.verifier.raw.claim.result = mmC := by
  rw [h]

/-! ## F-2 / F-3. Suppliers are lemmas; `hcoins` is an exists-in-the-proof. -/

/-- `hconf` is a lemma, polymorphic in the carrier -/
theorem b297_hconf_is_lemma {K : Type} [Field K] :
    TraceConfined 568 (airReorder (mmTree (K := K))) :=
  mm_traceConfined

/-- `hbad` is a lemma at the literal `seedZ` -/
theorem b297_hbad_is_lemma :
    seedZ ∉ (genSkeletonP8Census (K := GK) b296_hΛ
      (mmTree_gen (K := GK)) mm_traceConfined
      (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ)
        (mmTree (K := GK)))).census.badSeeds :=
  mm_hbad b296_hΛ

/-- `hcoins` exists as a compiler choice; it is not a public binder of `b296`. -/
theorem b297_hcoins_is_exists :
    ∃ a b c : GK,
      ComputeCoinsGeneric (K := GK) seedZ alphaA a b c
        (airReorder (mmTree (K := GK))) :=
  mm_exists_computeCoins

/-- Generic coin existence: row count `< |K|`, the §1 no-wraparound family. -/
theorem b297_coins_from_row_bound {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (z α : K) (t : NTree (GenComputeRow K))
    (hrow : (bfsForest [airReorder t]).length < Fintype.card K) :
    ∃ a b c : K, ComputeCoinsGeneric z α a b c (airReorder t) :=
  exists_computeCoinsGeneric_airReorder z α t hrow

/-! ## F-4. Scope: Goldilocks field-scope is disclosed, not hidden. -/

/-- Residuals that mention `K` after `open MatmulConfigGoldilocks` are Field.K. -/
theorem b297_residual_K_is_goldilocks
    (z α : Nock.Field.K) :
    0 < (bfsForest (genMemoryForest z α MemoryTable.formRDefault (memInputs z)
      (mmTree (K := Nock.Field.K)))).length :=
  mm_mempos z α

/-! ## F-5. No new failure-event summand. -/

/-- Instantiation does not add a coin/seed summand to the consumed bound. -/
theorem b297_bound_eq_p8_alpha_io
    (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedHostileProductionFailureProbabilityBound
      cardK cardF p8Work ioWork N M =
      (p8Work +
        OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
        pricedWalkWork N M : ℚ) /
          cardK +
      (ioWork : ℚ) / cardK ^ 2 +
      ((FiniteIO.ioFailureUnionBound 10 M M cardK + cardK * M : ℕ) : ℚ) /
          cardK ^ 2 :=
  optimizedHostileProductionFailureProbabilityBound_byte_identical
    cardK cardF p8Work ioWork N M

end

end Nock.RedTeam.Batch297

#print axioms Nock.RedTeam.Batch297.b297_instance_nonvacuous
#print axioms Nock.RedTeam.Batch297.b297_hconf_is_lemma
#print axioms Nock.RedTeam.Batch297.b297_hbad_is_lemma
#print axioms Nock.RedTeam.Batch297.b297_hcoins_is_exists
#print axioms Nock.RedTeam.Batch297.b297_bound_eq_p8_alpha_io
#print axioms Nock.RedTeam.Batch296.b296_nockCompiles_literal
#print axioms Nock.RedTeam.Batch296.b296_evalN
