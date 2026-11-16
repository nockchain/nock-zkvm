/-
  Nock/RedTeam/Batch298Thm54GenericHmempos.lean

  **Generic leftover (1): `hmempos` is a theorem of `genComputeSkeleton`,
  not a fixture and not a `∀ E` field.**

  (re-read): `mem_record₁` always verifies the
  opening of the formula.  That is the full compute-table ISA (`s0`–`s9`
  and `cons`); `recordCount_pos` is `1 ≤ recordCount s` at every state.
  The generator emits that formula-open request on every successful arm
  (`genComputeSkeleton_root_requests`).  So
  `genComputeSkeleton_hmempos` discharges
  `0 < (bfsForest (genMemoryForest z α inp t)).length` from `h` alone.

  `nockCompiles_of_grom_atTree_p62` no longer binds `hmempos`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenericMempos
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksResiduals

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Lean Elab Command

namespace Batch298BinderWalk

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
  let n65 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p65
  let e62 ← liftTermElabM (explicitNames n62)
  let e64 ← liftTermElabM (explicitNames n64)
  let e65 ← liftTermElabM (explicitNames n65)
  if e62.contains `hmempos then
    throwError m!"of_grom_atTree_p62 still has hmempos"
  unless e64.contains `hmempos do
    throwError m!"p64 dropped hmempos (Batch290 pin is 42/24)"
  if e65.contains `hmempos then
    throwError m!"p65 still has hmempos"
  logInfo m!"BINDER-DIFF p62/p65 have no hmempos; p64 keeps it (pin)"

end Batch298BinderWalk

namespace Nock.RedTeam.Batch298

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open MemoryTable

abbrev DK := DotConfig769.K
abbrev GK := Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.K

/-! ## Generic lemma, two inhabitants, no fixture `mm_mempos`. -/

/-- The lemma is `∀` accepted `genComputeSkeleton`, any `z`/`α`/`inp`. -/
theorem b298_hmempos_of_gen {K : Type} [Field K]
    (z α : K) (inp : Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    0 < (bfsForest (genMemoryForest z α MemoryTable.formRDefault inp t)).length :=
  genComputeSkeleton_hmempos z α inp h

/-- Tier A: same fact as `Batch216.b216_mempos`, from the generic lemma. -/
theorem b298_hmempos_dot (z α : DK) :
    0 < (bfsForest (genMemoryForest z α MemoryTable.formRDefault (memInputs z) (dotTree (K := DK)))).length :=
  genComputeSkeleton_hmempos z α (memInputs z) (genComputeSkeleton_dot (K := DK) 0)

theorem b298_hmempos_mm (z α : GK) :
    0 < (bfsForest (genMemoryForest z α MemoryTable.formRDefault (memInputs z)
      (mmTree (K := GK)))).length :=
  genComputeSkeleton_hmempos z α (memInputs z) (mmTree_gen (K := GK))

end Nock.RedTeam.Batch298

#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_hmempos
#print axioms Nock.RedTeam.Batch298.b298_hmempos_of_gen
#print axioms Nock.RedTeam.Batch298.b298_hmempos_dot
#print axioms Nock.RedTeam.Batch298.b298_hmempos_mm
