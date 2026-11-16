/-
  Nock/RedTeam/Batch300Thm54P5NockCompilesP67.lean

  Brief asked for `Batch298Thm54P5NockCompilesP64`; that filename is
  taken (`Batch298Thm54GenericHmempos`).  This is the chosen-seed
  inhabitant: `romSeedVcompOfWindow` stays `Classical.choose`, and
  every count binder is seed-free (`0` dummy + irrel).  Same
  conclusion as `b296` (`claim = ⟨mmSubject, mmFormula, mmC⟩`).
  Zero explicit binders.
-/
import Lean
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulBounded
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulConfigGoldilocks
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksResiduals
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulTraceConfined
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.NockVMROM.Thm54.TraceGen.GenSeedVcomp
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Nock.RedTeam.Batch300

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks
open Nock.NockVMROM.Thm54.TraceGen.GoodSeed
open Nock.Framework.Thm54

abbrev GF := MatmulConfigGoldilocks.F
abbrev GK := MatmulConfigGoldilocks.K

local instance charRingGK : CharP GK (ringChar GK) := ringChar.charP GK

noncomputable local instance : Fintype GK := Fintype.ofFinite _
noncomputable local instance : DecidableEq GK := Classical.decEq _

noncomputable section

noncomputable def b300_claimed_is_mmC : mmC =
    .cell (.cell (.atom 2) (.atom 1)) (.cell (.atom 1) (.atom 1)) :=
  rfl

/-- `romTree` of the guarded run is the generated `mmTree`. -/
noncomputable def b300_rom_eq_mm :
    romTree (K := GK) (evalGRom_le_evalRom mm_grom) = mmTree (K := GK) :=
  (mmTree_eq_of_gen (K := GK)
    (romTree_spec (K := GK) (evalGRom_le_evalRom mm_grom))).symm

noncomputable def b300_assign_rows :
    (bfsForest [bfsAssign (airReorder (mmTree (K := GK)))]).length = 401 := by
  rw [bfsForest_bfsAssign_length]
  have hsz : (airReorder (mmTree (K := GK))).size = 401 := by
    rw [airReorder_size, mmTree_size]
  simp [bfsForest_length, totalSize] at hsz ⊢
  exact hsz

/-- Joint seed budget at 401 AIR-ordered rows / `Λ = 568` sits under `|K|`. -/
noncomputable def b300_hseedcard :
    seedBudgetVcomp 568
      (bfsForest [bfsAssign (airReorder (mmTree (K := GK)))]).length
      < Fintype.card GK := by
  have hsq : sizeWindowRootBound 568 ≤ 568 * 568 :=
    sizeWindowRootBound_le_square 568
  rw [b300_assign_rows, Field.card_K]
  unfold seedBudgetVcomp seedBudget
  simp only [Field.p] at hsq ⊢
  omega

noncomputable def b300_hcomp :
    (bfsRows (airReorder (mmTree (K := GK)))).length
      ≤ 2 ^ executionOrbit.h := by
  rw [← genComputeRows_bfsForest_length (0 : GK) alphaA]
  exact mm_hcomp (0 : GK) alphaA

theorem b300_hrows :
    3 * (bfsRows (airReorder (mmTree (K := GK)))).length < ringChar GK ∧
      programMemShape alphaA (mmTree (K := GK)) < ringChar GK := by
  have h1 := mm_hcomp (0 : GK) alphaA
  rw [genComputeRows_bfsForest_length] at h1
  have h2 : programMemShape alphaA (mmTree (K := GK)) ≤ 2 ^ executionOrbit.h := by
    rw [programMemShape_spec (lmb := MemoryTable.formRDefault) 0]
    exact mm_hmem (0 : GK) alphaA
  rw [executionOrbit_h] at h1 h2
  rw [← hchar]
  simp only [Field.p]
  constructor <;> omega

/-- **`nockCompiles_p67` at the Goldilocks 2×2 matmul.**
    Chosen seed is compiler `∃`; counts are dummy-`0` + irrel.
    Claim is the program triple; `mmC` is `evalN`'s result.
    Form R leftover `hfirst`/`hmore` are dummy-applied. -/
noncomputable def b300_nockCompiles_p67_literal :=
  nockCompiles_p67 (hF := GeneratedField.primeFieldElems_zmod _) (hrows := by rw [b300_rom_eq_mm]; exact b300_hrows) (F := GF) (q := Field.p) (Λ := 568)
    alphaA alphaA MemoryTable.formRDefault two_ne_zero
    mm_grom mmSubject_bounded_p mmFormula_bounded_p
    (by rw [b300_rom_eq_mm]; exact mm_traceConfined)
    (by rw [b300_rom_eq_mm]; exact b300_hseedcard)
    hq hchar
    executionOrbit horb
    (by rw [b300_rom_eq_mm]; exact b300_hcomp)
    (by rw [b300_rom_eq_mm, programMemShape_spec (lmb := MemoryTable.formRDefault) 0]
        exact mm_hmem (0 : GK) alphaA)
    (by rw [b300_rom_eq_mm]; exact mm_hwin)
    (by rw [b300_rom_eq_mm]; exact mm_hmemOrd)
    (by rw [b300_rom_eq_mm, ← compilerKszOf_eq_L]; exact mm_hKszChar (0 : GK) alphaA)
    (by rw [b300_rom_eq_mm]; exact mm_hprogCap)
    (by rw [b300_rom_eq_mm]; exact mm_hmemCap (0 : GK) alphaA)
    basis packageOrbit hcap
    (by rw [b300_rom_eq_mm, ← compilerNOf_eq_L]; exact mm_hcard (0 : GK) alphaA)

end

end Nock.RedTeam.Batch300

open Lean Elab Command Meta

namespace Batch300BinderWalk

def binderTelescope (n : Name) : MetaM (Array (Name × BinderInfo)) := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs _ =>
    xs.mapM fun x => do
      let l ← x.fvarId!.getDecl
      pure (l.userName, l.binderInfo)

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
  let n64 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p64
  let n65 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p65
  let n66 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p66
  let n67 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p67
  let n300 : Name := ``Nock.RedTeam.Batch300.b300_nockCompiles_p67_literal
  let e64 ← liftTermElabM (explicitNames n64)
  let e65 ← liftTermElabM (explicitNames n65)
  let e66 ← liftTermElabM (explicitNames n66)
  let e67 ← liftTermElabM (explicitNames n67)
  let (t64, expl64, _) ← liftTermElabM (binderCounts n64)
  let (t65, expl65, _) ← liftTermElabM (binderCounts n65)
  let (t66, expl66, _) ← liftTermElabM (binderCounts n66)
  let (t67, expl67, _) ← liftTermElabM (binderCounts n67)
  let (t300, expl300, _) ← liftTermElabM (binderCounts n300)
  unless e64.contains `hmempos do
    throwError m!"p64 dropped hmempos (Batch290 pin)"
  if e65.contains `hmempos then
    throwError m!"p65 still has hmempos"
  if e66.contains `hconf then
    throwError m!"p66 still has a separate hconf"
  if e66.contains `hwinNouns then
    throwError m!"p66 still has hwinNouns"
  if expl300 ≠ 5 then
    throwError m!"b300 explicit binders: got {expl300}, expected 5 (hfirst/hmore/hax/hbasis/hwidth)"
  logInfo m!"BINDER-WALK p64={t64}/{expl64} p65={t65}/{expl65} p66={t66}/{expl66} p67={t67}/{expl67} b300={t300}/{expl300}"
  logInfo m!"BINDER-NAMES p64={e64} p65={e65} p66={e66} p67={e67}"

end Batch300BinderWalk

#print axioms Nock.RedTeam.Batch300.b300_nockCompiles_p67_literal
#print axioms Nock.RedTeam.Batch300.b300_hseedcard
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p67
