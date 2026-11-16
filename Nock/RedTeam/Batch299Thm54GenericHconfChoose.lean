/-
  Nock/RedTeam/Batch299Thm54GenericHconfChoose.lean

  Leftover (2).  `TraceConfined Λ t ↔ programLeafBound t ≤ Λ`
  (`traceConfined_iff_leafBound`, `GenTraceConfined.lean`).  That is the
  Lean image of §1 `hΛ : leafBound … ≤ Λ`: membership, not a growth invariant.  Reasons, compiled
  below: `hbad` types through `genSkeletonP8Census` which takes `hconf`;
  `romSeedVcomp` takes `hconf`; proving the numeral at a concrete
  program is still the opcode combinator spine
  (`confined_gen_op0` / … / slam).  Not a sixth §1 premise: it *is*
  §1 `hΛ`.  Dummy `1 ≤ Λ` is padding of `RowLeafWindow`.

  Leftover (3).  `romSeedVcomp` is definitionally
  `exists_vcomp_seed_of_rom.choose`.  `choose_spec` is already
  `romSeedVcomp_seedGood` / `_ne_zero` / `_notMem_badSeeds`.  The
  inhabited path is `nockCompiles_of_grom_atTree_p62` at a literal
  `seedZ`.  Replacing choose with that path
  generically would add a named seed witness — a new `∀` binder.
  Firing `p64` via choose is not §1.
-/
import Lean
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.NockVMROM.Thm54.TraceGen.GenSeedVcomp
import Nock.NockVMROM.Thm54.TraceGen.GenTraceConfined

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Lean Elab Command

namespace Batch299BinderWalk

open Lean Meta Elab

def binderTelescope (n : Name) : MetaM (Array (Name × BinderInfo)) := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs _ =>
    xs.mapM fun x => do
      let l ← x.fvarId!.getDecl
      pure (l.userName, l.binderInfo)

def explicitNames (n : Name) : MetaM (Array Name) := do
  let tel ← binderTelescope n
  return tel.filterMap fun (nm, bi) =>
    if bi == .default then some nm else none

run_cmd do
  let n62 : Name := ``Nock.NockVMROM.Thm54.TraceGen.nockCompiles_of_grom_atTree_p62
  let n64 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p64
  let e62 ← liftTermElabM (explicitNames n62)
  let e64 ← liftTermElabM (explicitNames n64)
  unless e62.contains `hconf do
    throwError m!"p62 dropped hconf (leftover 2 STOP: keep the window binder)"
  unless e64.contains `hconf do
    throwError m!"p64 dropped hconf (leftover 2 STOP: romSeedVcomp takes it)"
  unless e64.contains `hgrom do
    throwError m!"p64 dropped hgrom (still the ∀-program form)"
  logInfo m!"BINDER-DIFF leftover 2 STOP: p62/p64 keep hconf; leftover 3: p64 keeps hgrom"

end Batch299BinderWalk

namespace Nock.RedTeam.Batch299

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TraceGen.GoodSeed

variable {K : Type} [Field K]

/-! ## Leftover 2: the window is `leafBound`, equivalently `TraceConfined`. -/

/-- **Generic:** `TraceConfined` is the §1 window numeral, not a sixth binder
and not `∀ program` without a window -/
theorem b299_confined_iff_leafBound {Λ : ℕ} {t : NTree (GenComputeRow K)} :
    TraceConfined Λ t ↔ programLeafBound t ≤ Λ :=
  traceConfined_iff_leafBound

theorem b299_traceConfined_of_hΛ {Λ : ℕ} {t : NTree (GenComputeRow K)}
    (hΛ : programLeafBound t ≤ Λ) : TraceConfined Λ t :=
  traceConfined_of_hΛ hΛ

/-- Padding `1 ≤ Λ` is implied by a nonempty confined tree.  Not a growth
invariant. -/
theorem b299_one_le_of_hconf {Λ : ℕ} {t : NTree (GenComputeRow K)}
    (hrows : 0 < (bfsRows t).length) (h : TraceConfined Λ t) : 1 ≤ Λ :=
  one_le_of_traceConfined hrows h

/-! ## Leftover 3: choose is the compiler `∃`, not a residual. -/

/-- `romSeedVcomp` is definitionally `Classical.choose` of the joint
pigeonhole.  `choose_spec` is already compiled. -/
theorem b299_romSeedVcomp_is_choose [Fintype K] [DecidableEq K]
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

/-- The existence half is already a theorem; choose does not hide a missing
`choose_spec` -/
theorem b299_choose_spec_seedGood [Fintype K] [DecidableEq K]
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

/-- The joint pigeonhole is inhabited in the abstract: a seed exists for
every accepted ROM run under the seed-budget.  That is the compiler `∃`. -/
theorem b299_exists_vcomp_seed_of_rom [Fintype K] [DecidableEq K]
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
    ∃ z : K, z ≠ 0
      ∧ z ∉ (genSkeletonP8Census (K := K) hΛ (romTree_spec (K := K) hrom) hconf
              (genMemoryForest z α MemoryTable.formRDefault (memInputs z) (romTree (K := K) hrom))).census.badSeeds
      ∧ z ∉ sizeWindowFailureSeeds (K := K)
              (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
                (genMemoryForest z α MemoryTable.formRDefault (memInputs z) (romTree (K := K) hrom)))
      ∧ SeedGood z (romTree (K := K) hrom) :=
  exists_vcomp_seed_of_rom hq hchar hs hf hG hrom hΛ hconf α hwin hcard

end Nock.RedTeam.Batch299

#print axioms Nock.RedTeam.Batch299.b299_confined_iff_leafBound
#print axioms Nock.RedTeam.Batch299.b299_traceConfined_of_hΛ
#print axioms Nock.RedTeam.Batch299.b299_one_le_of_hconf
#print axioms Nock.RedTeam.Batch299.b299_romSeedVcomp_is_choose
#print axioms Nock.RedTeam.Batch299.b299_choose_spec_seedGood
#print axioms Nock.RedTeam.Batch299.b299_exists_vcomp_seed_of_rom
