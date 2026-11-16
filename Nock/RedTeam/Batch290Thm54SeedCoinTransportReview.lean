/-
  Nock/RedTeam/Batch290Thm54SeedCoinTransportReview.lean

  Did not write the restatements.

  Paper re-read at source: `:1090-1099`, `:1097`, `:1160`, `:1188`,
  `:1450`, `:1706`, `:1893`.

  Every named theorem `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
  No production file under `Nock/NockVMROM/` is edited.
-/
import Lean
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.NockVMROM.Thm54.TraceGen.GenSeedVcomp
import Nock.NockVMROM.Thm54.TraceGen.GenConsHead
import Nock.NockVMROM.Thm54.TraceGen.GenCoinCounting
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.RedTeam.Batch246Thm54InputsAtGeneratedCarrier
import Nock.RedTeam.Batch261Thm54GoodSeedAtTierA
import Nock.RedTeam.Batch288Thm54P63SeedCoins
import Nock.RedTeam.Batch289Thm54P64SeedConcretization
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open Lean Elab Command Meta

-- Namespace them; theorems unchanged.
namespace Batch290BinderWalk

/-- Binder telescope of a constant's type (instances and implicits included). -/
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

/-- Names of default (explicit) binders, in telescope order. -/
def explicitNames (n : Name) : MetaM (Array Name) := do
  let tel ← binderTelescope n
  return tel.filterMap fun (nm, bi) =>
    if bi == .default then some nm else none

run_cmd do
  let check (n : Name) (total expl : Nat) : CommandElabM Unit := do
    let (t, e, _i) ← liftTermElabM (binderCounts n)
    if t ≠ total || e ≠ expl then
      throwError m!"binder count {n}: got total {t} explicit {e}, expected {total}/{expl}"
    logInfo m!"BINDER-COUNT {n} total={t} explicit={e}"
  let n62 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p62
  let n63 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p63
  let n64 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p64
  check n62 57 39
  check n63 53 35
  check n64 52 34
  let e62 ← liftTermElabM (explicitNames n62)
  let e63 ← liftTermElabM (explicitNames n63)
  let e64 ← liftTermElabM (explicitNames n64)
  for nm in e63 do
    unless e62.contains nm do
      throwError m!"P6.3 added explicit binder {nm}"
  for nm in e64 do
    unless e63.contains nm do
      throwError m!"P6.4 added explicit binder {nm}"
  let dropped63 : Array Name := #[`a, `b, `c, `hcoins]
  for nm in dropped63 do
    unless e62.contains nm do
      throwError m!"P6.2 missing expected drop-candidate {nm}"
    if e63.contains nm then
      throwError m!"P6.3 still has {nm}"
  unless e63.contains `hseed do
    throwError m!"P6.3 missing hseed (should remain)"
  if e64.contains `hseed then
    throwError m!"P6.4 still has hseed"
  unless e62.size = e63.size + 4 do
    throwError m!"P6.3 net drop is not 4 explicit binders"
  unless e63.size = e64.size + 1 do
    throwError m!"P6.4 net drop is not 1 explicit binder"
  logInfo m!"BINDER-DIFF p63 explicit names ⊆ p62; dropped a,b,c,hcoins"
  logInfo m!"BINDER-DIFF p64 explicit names ⊆ p63; dropped hseed"

end Batch290BinderWalk

namespace Nock.RedTeam.Batch290

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.NockVMROM.Thm54.TraceGen.GoodSeed
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.CensusExtraClosure
open Nock.Framework.Thm54
open Nock.RedTeam
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open ComputeTable
open scoped Classical

abbrev DK := DotConfig769.K
abbrev DF := DotConfig769.F

local instance charRingDK : CharP DK (ringChar DK) := ringChar.charP DK




noncomputable section

/-! ## F-1. Claim conjunct is the evaluation result. -/

/-- `hgrom` is §1's `hrun`: a guarded ROM run is a reference-interpreter run. -/
theorem hgrom_implies_evalN {q fuel : ℕ} {subject formula result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result) :
    Nock.evalN fuel subject formula = some result :=
  evalGRom_evalN hgrom

/-- Tier A's `hgrom` is the same `result` the package claims. -/
theorem b290_tierA_grom_evalN :
    Nock.evalN 4 dotSubject dotFormula = some dotResult :=
  evalGRom_evalN Batch263.b263_grom

/-- Independent evalN pin of the same triple. -/
theorem b290_claimed_result_is_evalN :
    Nock.evalN 4 dotSubject dotFormula = some dotResult :=
  Batch246.b246_claim_evalN

noncomputable def b290_p63_claim_is_evalN :=
  fun hbasis hwidth hax =>
    (⟨Exists.imp (fun _ hp => ⟨hp.1, hp.2.1⟩) (Batch288.b288_nockCompiles_p63 hbasis hwidth hax),
      b290_claimed_result_is_evalN⟩ :
      (∃ package : OptimizedFullStrictNockVMROMPackage DF DK 8,
        OptimizedFullStrictThm54Statement package
          ∧ package.optimized.verifier.raw.claim =
            ⟨dotSubject, dotFormula, dotResult⟩)
      ∧ Nock.evalN 4 dotSubject dotFormula = some dotResult)

noncomputable def b290_p64_claim_is_evalN :=
  fun hbasis hwidth hax =>
    (⟨Exists.imp (fun _ hp => ⟨hp.1, hp.2.1⟩) (Batch289.b289_nockCompiles_literal hbasis hwidth hax),
      b290_claimed_result_is_evalN⟩ :
      (∃ package : OptimizedFullStrictNockVMROMPackage DF DK 8,
        OptimizedFullStrictThm54Statement package
          ∧ package.optimized.verifier.raw.claim =
            ⟨dotSubject, dotFormula, dotResult⟩)
      ∧ Nock.evalN 4 dotSubject dotFormula = some dotResult)

/-! ## F-2. No new summand; `rows < |K|` from `hseedcard`. -/

/-- No `computeCoinFailure`, no `seedBudgetVcomp`. -/
theorem b290_bound_eq_p8_alpha_io
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

theorem b290_rows_from_seedBudget {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {Λ rows : ℕ} (hΛ : 1 ≤ Λ)
    (h : seedBudget Λ rows < Fintype.card K) :
    rows < Fintype.card K :=
  rows_lt_card_of_seedBudget (K := K) hΛ h

/-- Same derivation at the AIR-ordered forest `exists_computeCoinsGeneric` reads. -/
theorem b290_air_rows_from_seedBudget {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {Λ : ℕ} (hΛ : 1 ≤ Λ) (t : NTree (GenComputeRow K))
    (h : seedBudget Λ (bfsForest [bfsAssign (airReorder t)]).length < Fintype.card K) :
    (bfsForest [airReorder t]).length < Fintype.card K :=
  airReorder_rows_lt_card_of_seedBudget (K := K) hΛ t h

/-- The coin triple is a compiler choice outside the existing counted set. -/
theorem b290_coins_from_row_bound {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (z α : K) (t : NTree (GenComputeRow K))
    (hrow : (bfsForest [airReorder t]).length < Fintype.card K) :
    ∃ a b c : K, ComputeCoinsGeneric z α a b c (airReorder t) :=
  exists_computeCoinsGeneric_airReorder z α t hrow

/-- Membership in that set is exactly failure of `ComputeCoinsGeneric`. -/
theorem b290_coin_failure_is_genericity {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (z α a b c : K) (u : NTree (GenComputeRow K)) :
    ComputeCoinsGeneric z α a b c u ↔ (a, b, c) ∉ computeCoinFailure z α u :=
  computeCoinsGeneric_iff_not_mem z α a b c u

theorem b290_vcomp_budget_is_compiler_numeral (Λ rows : ℕ) :
    seedBudgetVcomp Λ rows = seedBudget Λ rows + 3 * rows * (2 * Λ - 1) :=
  rfl

theorem b290_vcomp_still_gt_rows {Λ rows : ℕ} (hΛ : 1 ≤ Λ) :
    rows < seedBudgetVcomp Λ rows :=
  seedBudgetVcomp_gt_rows hΛ

/-- The joint budget still implies the coin-side `rows < |K|`. -/
theorem b290_rows_from_seedBudgetVcomp {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {Λ rows : ℕ} (hΛ : 1 ≤ Λ)
    (h : seedBudgetVcomp Λ rows < Fintype.card K) :
    rows < Fintype.card K :=
  rows_lt_card_of_seedBudgetVcomp (K := K) hΛ h

/-! ## F-3. The three `SeedGood` shapes are theorems of the generator. -/

/-- Cons formula-head is a cell, from `genComputeSkeleton` alone. -/
theorem b290_cons_head_from_generator {K : Type} [Field K]
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (u : NTree (GenComputeRow K)) (hu : InTree t u) :
    u.label.skel.state = State.cons →
      ∃ a b, formulaHead u.label.skel.formula = Noun.cell a b :=
  genComputeSkeleton_inTree_consHead h u hu

/-- OP5/OP3/cons leaf windows, from `hconf` + `hΛ`. -/
theorem b290_leaf_window_from_hconf {K : Type} [Field K]
    {Λ fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (hΛ : 1 ≤ Λ)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hconf : TraceConfined Λ (airReorder t)) :
    ∀ g ∈ bfsRows (airReorder t), RowLeafWindow Λ g.skel :=
  genComputeSkeleton_bfsRows_leafWindow_air hΛ h hconf

/-- OP5 `BoundedBy q`, from `hs`/`hf`/`hG`. -/
theorem b290_bounded_from_hs_hf_hG {K : Type} [Field K]
    {q fuel : ℕ} (hq : 1 < q)
    {subject formula : Noun} {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (u : NTree (GenComputeRow K)) (hu : InTree (airReorder t) u) :
    computeNodeBounded q u :=
  genComputeSkeleton_airReorder_inTree_bounded hq hs hf hG h u hu

/-- `hG` is not a new `nockCompiles` premise: it follows from `hgrom`. -/
theorem b290_hG_of_hgrom {q fuel : ℕ} {subject formula result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result) :
    FieldEmbedding.evalGBy q fuel subject formula = some result :=
  evalGRom_le_evalGBy hgrom

/-- The per-row Dyck-bad bound, with no shape hypothesis left. -/
theorem b290_rowBad_of_generated_no_shape_hyp {K : Type} [Field K]
    [Fintype K] [DecidableEq K]
    {q Λ : ℕ} (hq : 1 < q) (hle : q ≤ ringChar K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    {g : GenComputeRow K} (hg : g ∈ bfsRows (airReorder t)) :
    (Finset.univ.filter (fun z : K => ¬ RowSeedGood z g)).card ≤ 3 * (2 * Λ - 1) :=
  rowBad_card_le_of_generated hq hle hs hf hG h hΛ hconf hg

/-- `hseed` at the joint compiler seed is `choose_spec`. -/
theorem b290_hseed_is_choose_spec {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {q Λ : ℕ} (hq : 11 < q) (hchar : q = ringChar K)
    {fuel : ℕ} {subject formula result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hrom : evalRom fuel subject formula = some result)
    (hΛ : 1 ≤ Λ)
    (hconf : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) hrom))]).length
        < Fintype.card K) :
    SeedGood (romSeedVcomp hq hchar hs hf hG hrom hΛ hconf α hwin hcard)
      (romTree (K := K) hrom) :=
  romSeedVcomp_seedGood hq hchar hs hf hG hrom hΛ hconf α hwin hcard

/-! ## F-5. Literal seed vs `choose`. -/

/-- `romSeedVcomp` is definitionally `Classical.choose` of the joint existential. -/
theorem b290_romSeedVcomp_is_choose {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {q Λ : ℕ} (hq : 11 < q) (hchar : q = ringChar K)
    {fuel : ℕ} {subject formula result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hrom : evalRom fuel subject formula = some result)
    (hΛ : 1 ≤ Λ)
    (hconf : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) hrom))]).length
        < Fintype.card K) :
    romSeedVcomp hq hchar hs hf hG hrom hΛ hconf α hwin hcard =
      (exists_vcomp_seed_of_rom_allLambda hq hchar hs hf hG hrom hΛ hconf α hwin hcard).choose :=
  rfl

/-- The compiled `b289_seedZ_joint` statement is `≠ 0 ∧ SeedGood`, not the full `KM` triple. -/
theorem b290_seedZ_joint_is_ne_zero_and_seedGood :
    seedZ ≠ (0 : DK) ∧ SeedGood seedZ (dotTree (K := DK)) :=
  Batch289.b289_seedZ_joint

/-- `SeedGood` at Tier A holds for **every** seed (vacuous: no cons / OP5 / OP3 rows). -/
theorem b290_seedGood_vacuous_at_tierA (z : DK) :
    SeedGood z (dotTree (K := DK)) :=
  Batch180.dot_seedGood z

/-- The `KM` size-window half is *not* vacuous at the same program. -/
theorem b290_km_size_window_not_vacuous :
    (1 : DK) ∈ sizeWindowFailureSeeds (K := DK)
      (genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK))))
        (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))) :=
  Batch261.b261_one_mem_sizeWindowFailureSeeds

/-- `seedZ` does sit outside that size-window set (separate from `b289_seedZ_joint`). -/
theorem b290_seedZ_hout :
    seedZ ∉ sizeWindowFailureSeeds (K := DK)
      (genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK))))
        (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))) :=
  Batch180.dot_gen_hout

noncomputable def b290_literal_is_p63_witness :=
  Batch288.b288_nockCompiles_p63

end

end Nock.RedTeam.Batch290

#print axioms Nock.RedTeam.Batch290.hgrom_implies_evalN
#print axioms Nock.RedTeam.Batch290.b290_p63_claim_is_evalN
#print axioms Nock.RedTeam.Batch290.b290_p64_claim_is_evalN
#print axioms Nock.RedTeam.Batch290.b290_bound_eq_p8_alpha_io
#print axioms Nock.RedTeam.Batch290.b290_rows_from_seedBudget
#print axioms Nock.RedTeam.Batch290.b290_coins_from_row_bound
#print axioms Nock.RedTeam.Batch290.b290_vcomp_budget_is_compiler_numeral
#print axioms Nock.RedTeam.Batch290.b290_cons_head_from_generator
#print axioms Nock.RedTeam.Batch290.b290_leaf_window_from_hconf
#print axioms Nock.RedTeam.Batch290.b290_bounded_from_hs_hf_hG
#print axioms Nock.RedTeam.Batch290.b290_rowBad_of_generated_no_shape_hyp
#print axioms Nock.RedTeam.Batch290.b290_hseed_is_choose_spec
#print axioms Nock.RedTeam.Batch290.b290_romSeedVcomp_is_choose
#print axioms Nock.RedTeam.Batch290.b290_seedGood_vacuous_at_tierA
#print axioms Nock.RedTeam.Batch290.b290_km_size_window_not_vacuous
#print axioms Nock.RedTeam.Batch290.b290_literal_is_p63_witness
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p63
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p64
#print axioms Nock.RedTeam.Batch288.b288_nockCompiles_p63
#print axioms Nock.RedTeam.Batch289.b289_nockCompiles_literal
#print axioms Nock.RedTeam.Batch289.b289_seedZ_joint
