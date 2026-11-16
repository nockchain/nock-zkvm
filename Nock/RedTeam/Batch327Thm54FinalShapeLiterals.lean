/-
  Nock/RedTeam/Batch327Thm54FinalShapeLiterals.lean

  **Three landed literals re-derived from the final `nockCompiles`.**
  Each has 2 Form R leftover explicit binders.  The proof applies
  `GoodSeed.nockCompiles` after rewriting `romTree` to the concrete
  tree (`mmTree` / `dotTree` / `fibTree`) so `orbitHeight` does not
  whnf the forest.  `hF` is transported by
  `orbitHeight_le_of_le` + `dvd_card_sub_one_of_orbitHeight_le`.

  Explicit binders of the three literals (`BINDER-WALK matmul/tierA/fib`): 5 -> 2 each
  (measured 2/2 total/explicit). Explicit binders 2 -> 0: the three literals are closed terms.

  -- the paper
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

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Nock.RedTeam.Batch327

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

noncomputable local instance : Fintype GK := Fintype.ofFinite _
noncomputable local instance : DecidableEq GK := Classical.decEq _
noncomputable local instance : Fintype DK := Fintype.ofFinite _
noncomputable local instance : DecidableEq DK := Classical.decEq _
noncomputable local instance : Fintype FK := Fintype.ofFinite _
noncomputable local instance : DecidableEq FK := Classical.decEq _

noncomputable section

/-! ## Goldilocks 2×2 matmul (`b296` / `b300`) -- the paper -/

theorem b327_mm_run : Nock.evalN 64 mmSubject mmFormula = some mmC :=
  evalGRom_evalN mm_grom

theorem b327_mm_grom :
    evalGRom (ringChar GK) 64 mmSubject mmFormula = some mmC := by
  rw [MatmulConfigGoldilocks.ringChar_K]
  exact mm_grom

theorem b327_mm_bound : RunBoundedBy (ringChar GK) 64 mmSubject mmFormula :=
  runBoundedBy_of_grom b327_mm_grom

theorem b327_mm_rom :
    romTree (K := GK)
        (evalGRom_le_evalRom (evalGRom_of_runBounded b327_mm_run b327_mm_bound)) =
      mmTree (K := GK) :=
  (mmTree_eq_of_gen (K := GK)
      (romTree_spec (K := GK)
        (evalGRom_le_evalRom (evalGRom_of_runBounded b327_mm_run b327_mm_bound)))).symm

theorem b327_mm_hF16 : 3 * 2 ^ 16 ∣ Fintype.card GF - 1 := by
  have h := three_mul_two_pow_dvd_p_sub_one 16 (by norm_num)
  have hc : Fintype.card GF = Field.p := ZMod.card _
  rw [hc]; exact h

theorem b327_mm_hs : FieldEmbedding.BoundedBy (ringChar GK) mmSubject := by
  rw [MatmulConfigGoldilocks.ringChar_K]; exact mmSubject_bounded_p

theorem b327_mm_hf : FieldEmbedding.BoundedBy (ringChar GK) mmFormula := by
  rw [MatmulConfigGoldilocks.ringChar_K]; exact mmFormula_bounded_p

theorem b327_mm_hΛ : programLeafBound
    (airReorder (romTree (K := GK)
      (evalGRom_le_evalRom (evalGRom_of_runBounded b327_mm_run b327_mm_bound))))
    ≤ 568 := by
  rw [b327_mm_rom]; exact leafBound_of_traceConfined mm_traceConfined

theorem b327_mm_hΛp : (568 : ℕ) < ringChar GK := by
  rw [MatmulConfigGoldilocks.ringChar_K]; simp only [Field.p]; norm_num

theorem b327_mm_hp : 29 ≤ ringChar GK := by
  rw [MatmulConfigGoldilocks.ringChar_K]; simp only [Field.p]; norm_num

theorem b327_mm_hfit : programFit MatmulConfigGoldilocks.alphaA (mmTree (K := GK))
    ≤ 2 ^ 16 :=
  programFit_le_of_caps Batch300.b300_hcomp
    (by
      rw [programMemShape_spec (lmb := 0) (0 : GK)]
      exact mm_hmemCap (0 : GK) MatmulConfigGoldilocks.alphaA)
    mm_hprogCap

theorem b327_mm_hF_orbit : 3 * 2 ^ orbitHeight (programFit MatmulConfigGoldilocks.alphaA
      (romTree (K := GK)
        (evalGRom_le_evalRom (evalGRom_of_runBounded b327_mm_run b327_mm_bound))))
    ∣ Fintype.card GF - 1 := by
  rw [b327_mm_rom]
  exact dvd_card_sub_one_of_orbitHeight_le (F := GF)
    (orbitHeight_le_of_le (by norm_num : 1 ≤ (16 : ℕ)) b327_mm_hfit) b327_mm_hF16

theorem b327_mm_hwin' : programAcc
    (romTree (K := GK)
      (evalGRom_le_evalRom (evalGRom_of_runBounded b327_mm_run b327_mm_bound)))
    + 3 < orderOf MatmulConfigGoldilocks.alphaA := by
  rw [b327_mm_rom]; exact mm_hwin

/-- **Repair (ii).**  The memory half of §1's `hwin` (weakest form). -/
theorem b327_mm_hmemOrd' : programMemShape MatmulConfigGoldilocks.alphaA
    (romTree (K := GK)
      (evalGRom_le_evalRom (evalGRom_of_runBounded b327_mm_run b327_mm_bound)))
    ≤ orderOf MatmulConfigGoldilocks.alphaA := by
  rw [b327_mm_rom]; exact mm_hmemOrd

theorem b327_mm_hKsz' : compilerKszOf (0 : GK) MatmulConfigGoldilocks.alphaA
    (romTree (K := GK)
      (evalGRom_le_evalRom (evalGRom_of_runBounded b327_mm_run b327_mm_bound)))
    < ringChar GK := by
  rw [b327_mm_rom]; exact mm_hKszChar (0 : GK) MatmulConfigGoldilocks.alphaA

/-- Form R leftovers residual (first-row counts are `chainOneBitWeight`). -- the paper -/
noncomputable def b327_matmul_from_nockCompiles :=
  nockCompiles (F := GF) (K := GK) (Λ := 568)
    MatmulConfigGoldilocks.alphaA MatmulConfigGoldilocks.alphaA MemoryTable.formRDefault
    b327_mm_run b327_mm_bound b327_mm_hs b327_mm_hf b327_mm_hΛ b327_mm_hΛp
    b327_mm_hp
    (by rw [Algebra.ringChar_eq GF GK, MatmulConfigGoldilocks.ringChar_K]; simp only [Field.p]; norm_num)
    MatmulConfigGoldilocks.finrank_cubic b327_mm_hF_orbit
    b327_mm_hwin'
    -- Repair (ii): the memory half of `hwin` (weakest form).
    b327_mm_hmemOrd'
    b327_mm_hKsz'
    -- H1.5b Part 2a: `hrows` at the run tree.
    (by rw [b327_mm_rom]; exact Batch300.b300_hrows)

    (GeneratedField.primeFieldElems_zmod _)

/-! ## Tier A (`b289`) -- the paper -/

theorem b327_dot_run : Nock.evalN 4 dotSubject dotFormula = some dotResult :=
  Batch251.b251_rom_evalN

theorem b327_dot_grom :
    evalGRom (ringChar DK) 4 dotSubject dotFormula = some dotResult := by
  rw [DotConfig769.ringChar_K]
  exact Batch263.b263_grom

theorem b327_dot_bound : RunBoundedBy (ringChar DK) 4 dotSubject dotFormula :=
  runBoundedBy_of_grom b327_dot_grom

theorem b327_dot_rom :
    romTree (K := DK)
        (evalGRom_le_evalRom (evalGRom_of_runBounded b327_dot_run b327_dot_bound)) =
      dotTree (K := DK) := by
  have hspec := romTree_spec (K := DK)
      (evalGRom_le_evalRom (evalGRom_of_runBounded b327_dot_run b327_dot_bound))
  have hdot := genComputeSkeleton_dot (K := DK) 0
  rw [hdot] at hspec
  exact (congrArg Prod.fst (Except.ok.inj hspec)).symm

theorem b327_dot_hF8 : 3 * 2 ^ 8 ∣ Fintype.card DF - 1 := by
  rw [ZMod.card]
  exact DotConfig769.seven68_dvd

theorem b327_dot_fit :
    programFit DotConfig769.alphaA (dotTree (K := DK)) ≤ 2 ^ 8 := by
  have hcomp : programCompRows (dotTree (K := DK)) ≤ 2 ^ 8 := by
    dsimp [programCompRows]
    rw [← genComputeRows_bfsForest_length
      DotConfig769.seedZ DotConfig769.alphaA]
    exact Batch216.b216_comp_le
  have hmemCap : programMemShape DotConfig769.alphaA (dotTree (K := DK)) + 1
      ≤ 2 ^ 8 := by
    rw [programMemShape_spec DotConfig769.seedZ]
    exact Batch221.b221_hmemCap
  have hprog : programAcc (dotTree (K := DK)) + 1 ≤ 2 ^ 8 :=
    Batch221.b221_hprogCap
  exact programFit_le_of_caps hcomp hmemCap hprog

theorem b327_dot_hs : FieldEmbedding.BoundedBy (ringChar DK) dotSubject := by
  rw [DotConfig769.ringChar_K]; exact Batch263.b263_subject_bounded

theorem b327_dot_hf : FieldEmbedding.BoundedBy (ringChar DK) dotFormula := by
  rw [DotConfig769.ringChar_K]; exact Batch263.b263_formula_bounded

theorem b327_dot_hΛ : programLeafBound
    (airReorder (romTree (K := DK)
      (evalGRom_le_evalRom (evalGRom_of_runBounded b327_dot_run b327_dot_bound))))
    ≤ DotConfig769.Λ := by
  rw [b327_dot_rom]; exact leafBound_of_traceConfined Batch180.dot_air_traceConfined

theorem b327_dot_hΛp : DotConfig769.Λ < ringChar DK := by
  rw [DotConfig769.ringChar_K]; norm_num [DotConfig769.Λ]

theorem b327_dot_hp : 29 ≤ ringChar DK := by
  rw [DotConfig769.ringChar_K]; norm_num

theorem b327_dot_hF_orbit : 3 * 2 ^ orbitHeight (programFit DotConfig769.alphaA
      (romTree (K := DK)
        (evalGRom_le_evalRom (evalGRom_of_runBounded b327_dot_run b327_dot_bound))))
    ∣ Fintype.card DF - 1 := by
  rw [b327_dot_rom]
  exact dvd_card_sub_one_of_orbitHeight_le (F := DF)
    (orbitHeight_le_of_le (by norm_num : 1 ≤ (8 : ℕ)) b327_dot_fit)
    b327_dot_hF8

theorem b327_dot_hwin' : programAcc
    (romTree (K := DK)
      (evalGRom_le_evalRom (evalGRom_of_runBounded b327_dot_run b327_dot_bound)))
    + 3 < orderOf DotConfig769.alphaA := by
  rw [b327_dot_rom]; exact Batch286.b286_hwin

/-- **Repair (ii).**  The memory half of §1's `hwin` (weakest form). -/
theorem b327_dot_hmemOrd' : programMemShape DotConfig769.alphaA
    (romTree (K := DK)
      (evalGRom_le_evalRom (evalGRom_of_runBounded b327_dot_run b327_dot_bound)))
    ≤ orderOf DotConfig769.alphaA := by
  rw [b327_dot_rom]; exact Batch285.b285_dot_hmemOrd

theorem b327_dot_hKsz' : compilerKszOf (0 : DK) DotConfig769.alphaA
    (romTree (K := DK)
      (evalGRom_le_evalRom (evalGRom_of_runBounded b327_dot_run b327_dot_bound)))
    < ringChar DK := by
  rw [b327_dot_rom, compilerKszOf_irrel (0 : DK) DotConfig769.seedZ,
    compilerKszOf_eq_L MemoryTable.formRDefault]
  exact Batch286.b286_hKszChar

/-- Form R leftovers residual (first-row counts are `chainOneBitWeight`). -- the paper -/
noncomputable def b327_tierA_from_nockCompiles :=
  nockCompiles (F := DF) (K := DK) (Λ := DotConfig769.Λ)
    DotConfig769.alphaA DotConfig769.alphaA MemoryTable.formRDefault
    b327_dot_run b327_dot_bound b327_dot_hs b327_dot_hf b327_dot_hΛ b327_dot_hΛp
    b327_dot_hp
    (by rw [Algebra.ringChar_eq DF DK, DotConfig769.ringChar_K]; norm_num)
    DotConfig769.finrank_cubic b327_dot_hF_orbit
    b327_dot_hwin'
    -- Repair (ii): the memory half of `hwin` (weakest form).
    b327_dot_hmemOrd'
    b327_dot_hKsz'
    (by rw [b327_dot_rom]; exact Batch285.b285_dot_hrows)

    (GeneratedField.primeFieldElems_zmod _)


/-! ## Peano-fib -- the paper -/

theorem b327_fib_run : Nock.evalN 32 fibSubject fibFormula = some fibResult :=
  fib_evalN

theorem b327_fib_grom :
    evalGRom (ringChar FK) 32 fibSubject fibFormula = some fibResult := by
  rw [FibConfigGoldilocks.ringChar_K]
  exact fib_grom

theorem b327_fib_bound : RunBoundedBy (ringChar FK) 32 fibSubject fibFormula :=
  runBoundedBy_of_grom b327_fib_grom

theorem b327_fib_rom :
    romTree (K := FK)
        (evalGRom_le_evalRom (evalGRom_of_runBounded b327_fib_run b327_fib_bound)) =
      fibTree (K := FK) :=
  (fibTree_eq_of_gen
      (romTree_spec (K := FK)
        (evalGRom_le_evalRom (evalGRom_of_runBounded b327_fib_run b327_fib_bound)))).symm

theorem b327_fib_hF16 : 3 * 2 ^ 16 ∣ Fintype.card FF - 1 := by
  have h := three_mul_two_pow_dvd_p_sub_one 16 (by norm_num)
  have hc : Fintype.card FF = Field.p := ZMod.card _
  rw [hc]; exact h

theorem b327_fib_fit :
    programFit FibConfigGoldilocks.alphaA (fibTree (K := FK)) ≤ 2 ^ 16 := by
  have hcomp : programCompRows (fibTree (K := FK)) ≤ 2 ^ 16 :=
    fib_p67_hcomp
  have hmemCap : programMemShape FibConfigGoldilocks.alphaA (fibTree (K := FK)) + 1
      ≤ 2 ^ 16 := by
    rw [programMemShape_spec (0 : FK)]
    exact fib_hmemCap (0 : FK) FibConfigGoldilocks.alphaA
  have hprog : programAcc (fibTree (K := FK)) + 1 ≤ 2 ^ 16 :=
    fib_hprogCap
  exact programFit_le_of_caps hcomp hmemCap hprog

theorem b327_fib_hs : FieldEmbedding.BoundedBy (ringChar FK) fibSubject := by
  rw [FibConfigGoldilocks.ringChar_K]; exact fibSubject_bounded_p

theorem b327_fib_hf : FieldEmbedding.BoundedBy (ringChar FK) fibFormula := by
  rw [FibConfigGoldilocks.ringChar_K]; exact fibFormula_bounded_p

theorem b327_fib_hΛ : programLeafBound
    (airReorder (romTree (K := FK)
      (evalGRom_le_evalRom (evalGRom_of_runBounded b327_fib_run b327_fib_bound))))
    ≤ 42 := by
  rw [b327_fib_rom]; exact leafBound_of_traceConfined fib_traceConfined

theorem b327_fib_hΛp : (42 : ℕ) < ringChar FK := by
  rw [FibConfigGoldilocks.ringChar_K]; simp only [Field.p]; norm_num

theorem b327_fib_hp : 29 ≤ ringChar FK := by
  rw [FibConfigGoldilocks.ringChar_K]; simp only [Field.p]; norm_num

theorem b327_fib_hF_orbit : 3 * 2 ^ orbitHeight (programFit FibConfigGoldilocks.alphaA
      (romTree (K := FK)
        (evalGRom_le_evalRom (evalGRom_of_runBounded b327_fib_run b327_fib_bound))))
    ∣ Fintype.card FF - 1 := by
  rw [b327_fib_rom]
  exact dvd_card_sub_one_of_orbitHeight_le (F := FF)
    (orbitHeight_le_of_le (by norm_num : 1 ≤ (16 : ℕ)) b327_fib_fit) b327_fib_hF16

theorem b327_fib_hwin' : programAcc
    (romTree (K := FK)
      (evalGRom_le_evalRom (evalGRom_of_runBounded b327_fib_run b327_fib_bound)))
    + 3 < orderOf FibConfigGoldilocks.alphaA := by
  rw [b327_fib_rom]; exact fib_hwin

/-- **Repair (ii).**  The memory half of §1's `hwin` (weakest form). -/
theorem b327_fib_hmemOrd' : programMemShape FibConfigGoldilocks.alphaA
    (romTree (K := FK)
      (evalGRom_le_evalRom (evalGRom_of_runBounded b327_fib_run b327_fib_bound)))
    ≤ orderOf FibConfigGoldilocks.alphaA := by
  rw [b327_fib_rom]; exact fib_hmemOrd

theorem b327_fib_hKsz' : compilerKszOf (0 : FK) FibConfigGoldilocks.alphaA
    (romTree (K := FK)
      (evalGRom_le_evalRom (evalGRom_of_runBounded b327_fib_run b327_fib_bound)))
    < ringChar FK := by
  rw [b327_fib_rom]; exact fib_hKszChar (0 : FK) FibConfigGoldilocks.alphaA

/-- Form R leftovers residual (first-row counts are `chainOneBitWeight`). -- the paper -/
noncomputable def b327_fib_from_nockCompiles :=
  nockCompiles (F := FF) (K := FK) (Λ := 42)
    FibConfigGoldilocks.alphaA FibConfigGoldilocks.alphaA MemoryTable.formRDefault
    b327_fib_run b327_fib_bound b327_fib_hs b327_fib_hf b327_fib_hΛ b327_fib_hΛp
    b327_fib_hp
    (by rw [Algebra.ringChar_eq FF FK, FibConfigGoldilocks.ringChar_K]; simp only [Field.p]; norm_num)
    FibConfigGoldilocks.finrank_cubic b327_fib_hF_orbit
    b327_fib_hwin'
    -- Repair (ii): the memory half of `hwin` (weakest form).
    b327_fib_hmemOrd'
    b327_fib_hKsz'
    (by rw [b327_fib_rom]; exact fib_hrows)

    (GeneratedField.primeFieldElems_zmod _)


end

end Nock.RedTeam.Batch327

open Lean Elab Command Meta

namespace Batch327BinderWalk

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
  let nMM : Name := ``Nock.RedTeam.Batch327.b327_matmul_from_nockCompiles
  let nTA : Name := ``Nock.RedTeam.Batch327.b327_tierA_from_nockCompiles
  let nFB : Name := ``Nock.RedTeam.Batch327.b327_fib_from_nockCompiles
  let (tMM, eMM, _) ← liftTermElabM (binderCounts nMM)
  let (tTA, eTA, _) ← liftTermElabM (binderCounts nTA)
  let (tFB, eFB, _) ← liftTermElabM (binderCounts nFB)
  unless eMM == 0 do
    throwError m!"matmul literal explicit: got {eMM}, expected 0"
  unless eTA == 0 do
    throwError m!"Tier A literal explicit: got {eTA}, expected 0"
  unless eFB == 0 do
    throwError m!"fib literal explicit: got {eFB}, expected 0"
  logInfo m!"BINDER-WALK matmul={tMM}/{eMM} tierA={tTA}/{eTA} fib={tFB}/{eFB}"

end Batch327BinderWalk

#print axioms Nock.RedTeam.Batch327.b327_matmul_from_nockCompiles
#print axioms Nock.RedTeam.Batch327.b327_tierA_from_nockCompiles
#print axioms Nock.RedTeam.Batch327.b327_fib_from_nockCompiles
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles
