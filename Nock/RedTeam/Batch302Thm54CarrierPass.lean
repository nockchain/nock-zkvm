/-
  Nock/RedTeam/Batch302Thm54CarrierPass.lean

  **Group 1 non-vacuity and converse for `nockCompiles_p68`.**

  Re-derives `b300_nockCompiles_p67_literal` from `nockCompiles_p68`
  (same Goldilocks 2×2, claim = ⟨mmSubject, mmFormula, mmC⟩).  Binder
  walk on `p68` / `p67_of_p68`.  Instrument: `Meta.forallTelescope` on
  `ConstantInfo.type`.

  Remaining explicit binders of the four partially applied literals
  (`b302p68/p69/p70/nockCompiles`): 5 -> 2 each; measured BINDER-WALK now
  p67=44/26 p68=38/20 p69=32/15 p70=32/15 nockCompiles=30/14.

  -- the paper
-/
import Lean
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulBounded
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulConfigGoldilocks
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksResiduals
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulTraceConfined
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.RedTeam.Batch300Thm54P5NockCompilesP67

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Nock.RedTeam.Batch302

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.GoldilocksOrbit
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks
open Nock.NockVMROM.Thm54.TraceGen.GoodSeed
open Nock.Framework.Thm54
open Nock.RedTeam.Batch300

abbrev GF := MatmulConfigGoldilocks.F
abbrev GK := MatmulConfigGoldilocks.K

local instance charRingGK : CharP GK (ringChar GK) := ringChar.charP GK

noncomputable local instance : Fintype GK := Fintype.ofFinite _
noncomputable local instance : DecidableEq GK := Classical.decEq _

noncomputable section

theorem b302_finrank : Module.finrank GF GK = 3 :=
  finrank_cubic

theorem b302_hF : 3 * 2 ^ 16 ∣ Fintype.card GF - 1 := by
  have h := three_mul_two_pow_dvd_p_sub_one 16 (by norm_num)
  have hc : Fintype.card GF = Field.p := ZMod.card _
  rw [hc]; exact h

theorem b302_hOrbPos : 1 ≤ (16 : ℕ) := by norm_num


theorem b302_hleaf : programLeafBound
    (airReorder (romTree (K := GK) (evalGRom_le_evalRom mm_grom))) ≤ 568 := by
  rw [b300_rom_eq_mm]; exact leafBound_of_traceConfined mm_traceConfined

theorem b302_hseed : seedBudgetVcomp 568
    (bfsForest [bfsAssign (airReorder
      (romTree (K := GK) (evalGRom_le_evalRom mm_grom)))]).length
    < Fintype.card GK := by
  rw [b300_rom_eq_mm]; exact b300_hseedcard

theorem b302_hcomp' :
    (bfsRows (airReorder
      (romTree (K := GK) (evalGRom_le_evalRom mm_grom)))).length
      ≤ 2 ^ 16 := by
  rw [b300_rom_eq_mm]
  have := b300_hcomp
  rw [executionOrbit_h] at this
  exact this

theorem b302_hmem' : programMemShape alphaA
    (romTree (K := GK) (evalGRom_le_evalRom mm_grom)) ≤ 2 ^ 16 := by
  rw [b300_rom_eq_mm, programMemShape_spec (0 : GK)]
  have := mm_hmem (0 : GK) alphaA
  rw [executionOrbit_h] at this
  exact this

theorem b302_hwin' : programAcc
    (romTree (K := GK) (evalGRom_le_evalRom mm_grom)) + 3
    < orderOf alphaA := by
  rw [b300_rom_eq_mm]; exact mm_hwin

/-- **Repair (ii).**  The memory half of §1's `hwin` (weakest form) at matmul. -/
theorem b302_hmemOrd' : programMemShape alphaA
    (romTree (K := GK) (evalGRom_le_evalRom mm_grom)) ≤ orderOf alphaA := by
  rw [b300_rom_eq_mm]; exact mm_hmemOrd

theorem b302_hKsz' : compilerKszOf (0 : GK) alphaA
    (romTree (K := GK) (evalGRom_le_evalRom mm_grom)) < ringChar GK := by
  rw [b300_rom_eq_mm]; exact mm_hKszChar (0 : GK) alphaA

theorem b302_hprog' : programAcc
    (romTree (K := GK) (evalGRom_le_evalRom mm_grom)) + 1
    ≤ 2 ^ 16 := by
  rw [b300_rom_eq_mm]
  have := mm_hprogCap
  rw [executionOrbit_h] at this
  exact this

theorem b302_hmemCap' : programMemShape alphaA
    (romTree (K := GK) (evalGRom_le_evalRom mm_grom)) + 1 ≤ 2 ^ 16 := by
  rw [b300_rom_eq_mm, programMemShape_spec (0 : GK)]
  have := mm_hmemCap (0 : GK) alphaA
  rw [executionOrbit_h] at this
  exact this

/-- `p < 2^64` at the Goldilocks prime (28th λ pass 2: `hp64` replaces `hwidth`/`hax`). -/
theorem b302_hp64 : ringChar GF < 2 ^ 64 := by
  rw [Algebra.ringChar_eq GF GK, MatmulConfigGoldilocks.ringChar_K]; simp only [Field.p]; norm_num

/-- Form R leftovers residual (first-row counts are `chainOneBitWeight`). -- the paper -/
noncomputable def b302_nockCompiles_p68_literal :=
  nockCompiles_p68 (hFprime := GeneratedField.primeFieldElems_zmod _) (hrows := by rw [b300_rom_eq_mm]; exact b300_hrows) (F := GF) (q := Field.p) (Λ := 568) (hOrb := 16)
    alphaA alphaA MemoryTable.formRDefault two_ne_zero
    mm_grom mmSubject_bounded_p mmFormula_bounded_p
    b302_hleaf b302_hseed hq hchar b302_hp64
    b302_hOrbPos b302_finrank b302_hF
    b302_hcomp' b302_hmem' b302_hwin' b302_hmemOrd' b302_hKsz' b302_hprog' b302_hmemCap'


noncomputable def b302_b300_from_p68 :=
  b302_nockCompiles_p68_literal

/-- Four capacity hyps fold into `programFit ≤ 2^16`. -/
theorem b302_fit :
    programFit alphaA
      (romTree (K := GK) (evalGRom_le_evalRom mm_grom)) ≤ 2 ^ 16 := by
  have ht := b300_rom_eq_mm
  have hcomp :
      programCompRows
        (romTree (K := GK) (evalGRom_le_evalRom mm_grom)) ≤ 2 ^ 16 := by
    rw [ht]
    have := b300_hcomp
    rw [executionOrbit_h] at this
    exact this
  have hmemCap : programMemShape alphaA
      (romTree (K := GK) (evalGRom_le_evalRom mm_grom)) + 1 ≤ 2 ^ 16 := by
    rw [ht, programMemShape_spec (0 : GK)]
    have := mm_hmemCap (0 : GK) alphaA
    rw [executionOrbit_h] at this
    exact this
  have hprog : programAcc
      (romTree (K := GK) (evalGRom_le_evalRom mm_grom)) + 1 ≤ 2 ^ 16 := by
    rw [ht]
    have := mm_hprogCap
    rw [executionOrbit_h] at this
    exact this
  exact programFit_le_of_caps hcomp hmemCap hprog

theorem b302_hF_orbit :
    3 * 2 ^ orbitHeight (programFit alphaA
        (romTree (K := GK) (evalGRom_le_evalRom mm_grom)))
      ∣ Fintype.card GF - 1 :=
  dvd_card_sub_one_of_orbitHeight_le (F := GF)
    (orbitHeight_le_of_le b302_hOrbPos b302_fit) b302_hF

/-- Form R leftovers residual via `p68_of_p69`. -- the paper -/
noncomputable def b302_b300_from_p69 :=
  nockCompiles_p68_of_p69 (hFprime := GeneratedField.primeFieldElems_zmod _) (hrows := by rw [b300_rom_eq_mm]; exact b300_hrows) (F := GF) (q := Field.p) (Λ := 568) (hOrb := 16)
    alphaA alphaA MemoryTable.formRDefault two_ne_zero
    mm_grom mmSubject_bounded_p mmFormula_bounded_p
    b302_hleaf b302_hseed hq hchar b302_hp64
    b302_hOrbPos b302_finrank b302_hF
    b302_hcomp' b302_hmem' b302_hwin' b302_hmemOrd' b302_hKsz' b302_hprog' b302_hmemCap'

/-- Form R leftovers residual (`p69` at fixture height 16). -- the paper -/
noncomputable def b302_nockCompiles_p69_literal :=
  b302_b300_from_p69

theorem b302_mm_run : Nock.evalN 64 mmSubject mmFormula = some mmC :=
  evalGRom_evalN mm_grom

theorem b302_mm_bound : RunBoundedBy Field.p 64 mmSubject mmFormula :=
  runBoundedBy_of_grom mm_grom

theorem b302_rom_run_eq_mm :
    romTree (K := GK)
        (evalGRom_le_evalRom (evalGRom_of_runBounded b302_mm_run b302_mm_bound)) =
      mmTree (K := GK) :=
  (romTree_grom_irrel (K := GK)
      (evalGRom_of_runBounded b302_mm_run b302_mm_bound) mm_grom).trans
    b300_rom_eq_mm

/-- Form R leftovers residual (`p70` / `nockCompiles` at 16). -- the paper -/
noncomputable def b302_nockCompiles_p70_literal :=
  b302_nockCompiles_p69_literal

/-- Final name, Form R leftovers residual. -- the paper -/
noncomputable def b302_nockCompiles_literal :=
  b302_nockCompiles_p69_literal


noncomputable def b302_b300_from_nockCompiles :=
  b302_nockCompiles_literal

end

end Nock.RedTeam.Batch302

open Lean Elab Command Meta

namespace Batch302BinderWalk

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
  let n67 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p67
  let n68 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p68
  let n69 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p69
  let n70 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p70
  let nNC : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles
  let nConv68 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p67_of_p68
  let nConv69 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p68_of_p69
  let nConv70 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p69_of_p70
  let n302 : Name := ``Nock.RedTeam.Batch302.b302_nockCompiles_p68_literal
  let n302b : Name := ``Nock.RedTeam.Batch302.b302_nockCompiles_p69_literal
  let n302c : Name := ``Nock.RedTeam.Batch302.b302_nockCompiles_p70_literal
  let n302d : Name := ``Nock.RedTeam.Batch302.b302_nockCompiles_literal
  let _e67 ← liftTermElabM (explicitNames n67)
  let e68 ← liftTermElabM (explicitNames n68)
  let e69 ← liftTermElabM (explicitNames n69)
  let e70 ← liftTermElabM (explicitNames n70)
  let eNC ← liftTermElabM (explicitNames nNC)
  let (t67, expl67, _) ← liftTermElabM (binderCounts n67)
  let (t68, expl68, _) ← liftTermElabM (binderCounts n68)
  let (t69, expl69, _) ← liftTermElabM (binderCounts n69)
  let (t70, expl70, _) ← liftTermElabM (binderCounts n70)
  let (tNC, explNC, _) ← liftTermElabM (binderCounts nNC)
  let (tConv68, explConv68, _) ← liftTermElabM (binderCounts nConv68)
  let (tConv69, explConv69, _) ← liftTermElabM (binderCounts nConv69)
  let (tConv70, explConv70, _) ← liftTermElabM (binderCounts nConv70)
  let (t302, expl302, _) ← liftTermElabM (binderCounts n302)
  let (t302b, expl302b, _) ← liftTermElabM (binderCounts n302b)
  let (t302c, expl302c, _) ← liftTermElabM (binderCounts n302c)
  let (t302d, expl302d, _) ← liftTermElabM (binderCounts n302d)
  if e68.contains `bas then
    throwError m!"p68 still has bas"
  if e69.contains `hcomp then
    throwError m!"p69 still has hcomp"
  if e69.contains `hprogCap then
    throwError m!"p69 still has hprogCap"
  if e70.contains `hgrom then
    throwError m!"p70 still has hgrom"
  unless e70.contains `hrun do
    throwError m!"p70 dropped hrun"
  unless e70.contains `hbound do
    throwError m!"p70 dropped hbound"
  unless eNC.contains `hrun do
    throwError m!"nockCompiles dropped hrun"
  if eNC.contains `hgrom then
    throwError m!"nockCompiles still has hgrom"
  if expl302 ≠ 0 then
    throwError m!"b302 p68 explicit binders: got {expl302}, expected 0"
  if expl302b ≠ 0 then
    throwError m!"b302 p69 explicit binders: got {expl302b}, expected 0"
  if expl302c ≠ 0 then
    throwError m!"b302 p70 explicit binders: got {expl302c}, expected 0"
  if expl302d ≠ 0 then
    throwError m!"b302 nockCompiles explicit binders: got {expl302d}, expected 0"
  logInfo m!"BINDER-WALK p67={t67}/{expl67} p68={t68}/{expl68} p69={t69}/{expl69} p70={t70}/{expl70} nockCompiles={tNC}/{explNC} p67_of_p68={tConv68}/{explConv68} p68_of_p69={tConv69}/{explConv69} p69_of_p70={tConv70}/{explConv70} b302p68={t302}/{expl302} b302p69={t302b}/{expl302b} b302p70={t302c}/{expl302c} b302nc={t302d}/{expl302d}"
  logInfo m!"BINDER-NAMES p68={e68} p69={e69} p70={e70} nockCompiles={eNC}"

end Batch302BinderWalk

#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p68
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p69
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p70
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles
#print axioms Nock.RedTeam.Batch302.b302_nockCompiles_p68_literal
#print axioms Nock.RedTeam.Batch302.b302_nockCompiles_p69_literal
#print axioms Nock.RedTeam.Batch302.b302_nockCompiles_p70_literal
#print axioms Nock.RedTeam.Batch302.b302_nockCompiles_literal
