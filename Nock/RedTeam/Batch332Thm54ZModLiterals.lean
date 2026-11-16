/-
  Nock/RedTeam/Batch332Thm54ZModLiterals.lean

  **Three landed literals re-derived from `nockCompiles_zmod`.**
  Each is 0 explicit binders.  The §1 spelling is applied at the literal
  prime (`Field.p` / `769`); `ringChar K = p` is derived inside the
  theorem, not assumed.

  Explicit binders of the three zmod literals: 5 -> 2 each (measured 2/2).
-/
import Lean
import Nock.NockVMROM.Thm54.GoldilocksOrbit
import Nock.NockVMROM.Thm54.TraceGen.GenFibInstances
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulBounded
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulConfigGoldilocks
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksResiduals
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulTraceConfined
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.RedTeam.Batch216Thm54SemanticCoverageAtTierA
import Nock.RedTeam.Batch221Thm54BuildableAtTierA
import Nock.RedTeam.Batch251Thm54NockCompiles
import Nock.RedTeam.Batch263Thm54BoundedPremisesAtTierA
import Nock.RedTeam.Batch286Thm54P62CapacityBinders
import Nock.RedTeam.Batch300Thm54P5NockCompilesP67
import Nock.RedTeam.Batch327Thm54FinalShapeLiterals
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Nock.RedTeam.Batch332

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.GoldilocksOrbit
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.GoodSeed
open Nock.Framework.Thm54
open Nock.RedTeam

abbrev GF := MatmulConfigGoldilocks.F
abbrev GK := MatmulConfigGoldilocks.K
abbrev DF := DotConfig769.F
abbrev DK := DotConfig769.K
abbrev FF := FibConfigGoldilocks.F
abbrev FK := FibConfigGoldilocks.K

local instance charRingGK : CharP GK (ringChar GK) := ringChar.charP GK
local instance charRingDK : CharP DK (ringChar DK) := ringChar.charP DK
local instance charRingFK : CharP FK (ringChar FK) := ringChar.charP FK

local instance : Fact (Nat.Prime 769) := ⟨by norm_num⟩

noncomputable local instance : Fintype GK := Fintype.ofFinite _
noncomputable local instance : DecidableEq GK := Classical.decEq _
noncomputable local instance : Fintype DK := Fintype.ofFinite _
noncomputable local instance : DecidableEq DK := Classical.decEq _
noncomputable local instance : Fintype FK := Fintype.ofFinite _
noncomputable local instance : DecidableEq FK := Classical.decEq _

noncomputable section

/-! ## Goldilocks 2×2 matmul -/

theorem b332_mm_bound : RunBoundedBy Field.p 64 mmSubject mmFormula :=
  runBoundedBy_of_grom mm_grom

theorem b332_mm_rom :
    romTree (K := GK)
        (evalGRom_le_evalRom (evalGRom_of_runBounded Batch327.b327_mm_run b332_mm_bound)) =
      mmTree (K := GK) :=
  (mmTree_eq_of_gen (K := GK)
      (romTree_spec (K := GK)
        (evalGRom_le_evalRom (evalGRom_of_runBounded Batch327.b327_mm_run b332_mm_bound)))).symm

/-- Form R leftovers residual (first-row counts are `chainOneBitWeight`) -/
noncomputable def b332_matmul_from_zmod :=
  nockCompiles_zmod (p := Field.p) (K := GK)
    MatmulConfigGoldilocks.alphaA MatmulConfigGoldilocks.alphaA MemoryTable.formRDefault
    Batch327.b327_mm_run b332_mm_bound
    mmSubject_bounded_p mmFormula_bounded_p
    (by
      change programLeafBound (airReorder (romTree (K := GK)
          (evalGRom_le_evalRom (evalGRom_of_runBounded Batch327.b327_mm_run b332_mm_bound))))
        < Field.p
      rw [b332_mm_rom]
      exact Nat.lt_of_le_of_lt
        (leafBound_of_traceConfined mm_traceConfined)
        (by simp only [Field.p]; norm_num))
    (by simp only [Field.p]; norm_num)
    (by simp only [Field.p]; norm_num)
    MatmulConfigGoldilocks.finrank_cubic
    (by
      have h := Batch327.b327_mm_hF_orbit
      simpa [ZMod.card, Field.p] using h)
    ⟨Batch327.b327_mm_hwin', Batch327.b327_mm_hmemOrd'⟩
    (by
      have h := Batch327.b327_mm_hKsz'
      simpa [MatmulConfigGoldilocks.ringChar_K] using h)

/-! ## Tier A at 769 -/

theorem b332_dot_bound : RunBoundedBy 769 4 dotSubject dotFormula :=
  runBoundedBy_of_grom Batch263.b263_grom

theorem b332_dot_rom :
    romTree (K := DK)
        (evalGRom_le_evalRom (evalGRom_of_runBounded Batch327.b327_dot_run b332_dot_bound)) =
      dotTree (K := DK) := by
  have hspec := romTree_spec (K := DK)
      (evalGRom_le_evalRom (evalGRom_of_runBounded Batch327.b327_dot_run b332_dot_bound))
  have hdot := genComputeSkeleton_dot (K := DK) 0
  rw [hdot] at hspec
  exact (congrArg Prod.fst (Except.ok.inj hspec)).symm

/-- Form R leftovers residual (first-row counts are `chainOneBitWeight`) -/
noncomputable def b332_tierA_from_zmod :=
  nockCompiles_zmod (p := 769) (K := DK)
    DotConfig769.alphaA DotConfig769.alphaA MemoryTable.formRDefault
    Batch327.b327_dot_run b332_dot_bound
    Batch263.b263_subject_bounded Batch263.b263_formula_bounded
    (by
      change programLeafBound (airReorder (romTree (K := DK)
          (evalGRom_le_evalRom (evalGRom_of_runBounded Batch327.b327_dot_run b332_dot_bound))))
        < 769
      rw [b332_dot_rom]
      exact Nat.lt_of_le_of_lt
        (leafBound_of_traceConfined Batch180.dot_air_traceConfined)
        (by
          have h := Batch327.b327_dot_hΛp
          simpa [DotConfig769.ringChar_K] using h))
    (by norm_num)
    (by norm_num)
    DotConfig769.finrank_cubic
    (by
      have h := Batch327.b327_dot_hF_orbit
      simpa [ZMod.card] using h)
    ⟨Batch327.b327_dot_hwin', Batch327.b327_dot_hmemOrd'⟩
    (by
      have h := Batch327.b327_dot_hKsz'
      simpa [DotConfig769.ringChar_K] using h)

/-! ## Peano-fib -/

theorem b332_fib_bound : RunBoundedBy Field.p 32 fibSubject fibFormula :=
  runBoundedBy_of_grom fib_grom

theorem b332_fib_rom :
    romTree (K := FK)
        (evalGRom_le_evalRom (evalGRom_of_runBounded Batch327.b327_fib_run b332_fib_bound)) =
      fibTree (K := FK) :=
  (fibTree_eq_of_gen
      (romTree_spec (K := FK)
        (evalGRom_le_evalRom (evalGRom_of_runBounded Batch327.b327_fib_run b332_fib_bound)))).symm

/-- Form R leftovers residual (first-row counts are `chainOneBitWeight`) -/
noncomputable def b332_fib_from_zmod :=
  nockCompiles_zmod (p := Field.p) (K := FK)
    FibConfigGoldilocks.alphaA FibConfigGoldilocks.alphaA MemoryTable.formRDefault
    Batch327.b327_fib_run b332_fib_bound
    fibSubject_bounded_p fibFormula_bounded_p
    (by
      change programLeafBound (airReorder (romTree (K := FK)
          (evalGRom_le_evalRom (evalGRom_of_runBounded Batch327.b327_fib_run b332_fib_bound))))
        < Field.p
      rw [b332_fib_rom]
      exact Nat.lt_of_le_of_lt
        (leafBound_of_traceConfined fib_traceConfined)
        (by simp only [Field.p]; norm_num))
    (by simp only [Field.p]; norm_num)
    (by simp only [Field.p]; norm_num)
    FibConfigGoldilocks.finrank_cubic
    (by
      have h := Batch327.b327_fib_hF_orbit
      simpa [ZMod.card, Field.p] using h)
    ⟨Batch327.b327_fib_hwin', Batch327.b327_fib_hmemOrd'⟩
    (by
      have h := Batch327.b327_fib_hKsz'
      simpa [FibConfigGoldilocks.ringChar_K] using h)

end

end Nock.RedTeam.Batch332

open Lean Elab Command Meta

namespace Batch332BinderWalk

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

run_cmd do
  let nMM : Name := ``Nock.RedTeam.Batch332.b332_matmul_from_zmod
  let nTA : Name := ``Nock.RedTeam.Batch332.b332_tierA_from_zmod
  let nFB : Name := ``Nock.RedTeam.Batch332.b332_fib_from_zmod
  let (tMM, eMM, _) ← liftTermElabM (binderCounts nMM)
  let (tTA, eTA, _) ← liftTermElabM (binderCounts nTA)
  let (tFB, eFB, _) ← liftTermElabM (binderCounts nFB)
  unless eMM == 0 do
    throwError m!"matmul zmod literal explicit: got {eMM}, expected 0"
  unless eTA == 0 do
    throwError m!"Tier A zmod literal explicit: got {eTA}, expected 0"
  unless eFB == 0 do
    throwError m!"fib zmod literal explicit: got {eFB}, expected 0"
  logInfo m!"BINDER-WALK matmul={tMM}/{eMM} tierA={tTA}/{eTA} fib={tFB}/{eFB}"

end Batch332BinderWalk

#print axioms Nock.RedTeam.Batch332.b332_matmul_from_zmod
#print axioms Nock.RedTeam.Batch332.b332_tierA_from_zmod
#print axioms Nock.RedTeam.Batch332.b332_fib_from_zmod
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
