/-
  Nock/RedTeam/Batch292Thm54P5GoldilocksRetarget.lean

  Retarget the 2×2 matmul onto Goldilocks so
  `packageOrbit` and the 30936-row forest can inhabit together.  This batch
  compiles that config (`MatmulConfigGoldilocks`) and the residuals that
  close on the new carrier.  It does **not** invent a 65537 orbit and does
  **not** pick 769.  `MatmulConfig65537` is intact.

  The fully-concrete `nockCompiles_of_grom_atTree_p62` instance is **not**
  claimed.  The first undischarged residual is `TraceConfined Λ
  (airReorder mmTree)` at `GaloisField Field.p 3`: `decide` does not reduce
  (`GenTraceConfined` docstring), and no constructor-induction / leaf-bound
  instance exists at the 401-row tree.  `exists_vcomp_seed_of_accepted`
  also wants `hconf`, so the choose-path is blocked by the same lemma.
  `SeedGood seedZ mmTree`, `hbad`, and `hout` remain open behind it.
-/
import Nock.Field
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulConfigGoldilocks
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksResiduals
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.RedTeam.Batch291Thm54P5FieldChoice
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch292

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.Framework.Thm54

abbrev GF := MatmulConfigGoldilocks.F
abbrev GK := MatmulConfigGoldilocks.K

/-! ## 1. The new config is Goldilocks, not 65537 and not 769. -/

theorem b292_field : GF = Field.Fp ∧ GK = Field.K := ⟨rfl, rfl⟩

theorem b292_not_65537 : Field.p ≠ 65537 := by
  simp only [Field.p]
  norm_num

theorem b292_finrank : Module.finrank GF GK = 3 := finrank_cubic

theorem b292_packageOrbit_order :
    orderOf packageOrbit.ω = 3 * 2 ^ 16 :=
  packageOrbit_order

theorem b292_executionOrbit_order :
    orderOf executionOrbit.ω = 2 ^ 16 :=
  executionOrbit_order

theorem b292_hosts_rows : 401 ≤ 2 ^ 16 ∧ 30936 ≤ 2 ^ 16 :=
  hosts_matmul_rows

theorem b292_same_packageOrbit_as_b291 :
    packageOrbit.ω = Batch291.b291_goldilocks_packageOrbit.ω :=
  rfl

/-! ## 2. Residuals that discharge on Goldilocks. -/

theorem b292_grom :
    evalGRom Field.p 64 mmSubject mmFormula = some mmC :=
  mm_grom

theorem b292_evalN {K' : Type} [Field K'] :
    Nock.evalN 64 mmSubject mmFormula = some mmC :=
  mm_evalN (K := K')

theorem b292_claimed_is_mmC : mmC =
    .cell (.cell (.atom 2) (.atom 1)) (.cell (.atom 1) (.atom 1)) :=
  rfl

theorem b292_row_counts :
    (exec seedZ alphaA).computeRows.length = 401 ∧
      (exec seedZ alphaA).memoryRows.length = 30936 :=
  exec_row_counts

theorem b292_hmempos :
    0 < (bfsForest (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ)
      (mmTree (K := GK)))).length :=
  mm_mempos seedZ alphaA

theorem b292_hcomp :
    (bfsForest [genComputeRows seedZ alphaA (mmTree (K := GK))]).length
      ≤ 2 ^ executionOrbit.h :=
  mm_hcomp seedZ alphaA

theorem b292_hmem :
    (bfsForest (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ)
      (mmTree (K := GK)))).length ≤ 2 ^ executionOrbit.h :=
  mm_hmem seedZ alphaA

theorem b292_hwin :
    programAcc (mmTree (K := GK)) + 3 <
      orderOf MatmulConfigGoldilocks.alphaA :=
  mm_hwin

theorem b292_hcard :
    RecordCarrier.honestIOBound
      (compilerNOf seedZ alphaA (mmTree (K := GK)))
      (compilerNOf seedZ alphaA (mmTree (K := GK)))
      (Fintype.card GK) < Fintype.card (GK × GK) :=
  mm_hcard seedZ alphaA

theorem b292_hKszChar :
    compilerKszOf seedZ alphaA (mmTree (K := GK)) < ringChar GK :=
  mm_hKszChar seedZ alphaA

theorem b292_hprogCap :
    programAcc (mmTree (K := GK)) + 1 ≤ 2 ^ executionOrbit.h :=
  mm_hprogCap

theorem b292_hmemCap :
    programMemRows seedZ alphaA (mmTree (K := GK)) + 1
      ≤ 2 ^ executionOrbit.h :=
  mm_hmemCap seedZ alphaA

theorem b292_exists_computeCoins :
    ∃ a b c : GK, ComputeCoinsGeneric seedZ alphaA a b c
      (airReorder (mmTree (K := GK))) :=
  mm_exists_computeCoins

theorem b292_bounded :
    FieldEmbedding.BoundedBy Field.p mmSubject ∧
      FieldEmbedding.BoundedBy Field.p mmFormula :=
  ⟨mmSubject_bounded_p, mmFormula_bounded_p⟩

theorem b292_hq : 11 < Field.p := hq
theorem b292_hchar : Field.p = ringChar GK := hchar
theorem b292_hz : seedZ ≠ 0 := seedZ_ne_zero
theorem b292_htwo : (2 : GK) ≠ 0 := two_ne_zero
theorem b292_hcap : 2 ^ executionOrbit.h ≤ 2 ^ (16 : ℕ) := hcap
theorem b292_mmSubject_leaves : mmSubject.leaves = 8 := mmSubject_leaves

/-! ## 3.

`nockCompiles_of_grom_atTree_p62` still wants
`hconf : TraceConfined Λ (airReorder mmTree)`.  `decide` does not reduce
at `GaloisField Field.p 3` (`GenTraceConfined`).  No 401-row leaf-window
instance exists.  `SeedGood`, `hbad`, and `hout` are not reached. -/

theorem b292_p62_still_wants_traceConfined :
    (∀ {Λ : ℕ}, TraceConfined Λ (airReorder (mmTree (K := GK))) → True) :=
  fun _ => trivial

end Nock.RedTeam.Batch292

#print axioms Nock.RedTeam.Batch292.b292_field
#print axioms Nock.RedTeam.Batch292.b292_packageOrbit_order
#print axioms Nock.RedTeam.Batch292.b292_grom
#print axioms Nock.RedTeam.Batch292.b292_evalN
#print axioms Nock.RedTeam.Batch292.b292_hcard
#print axioms Nock.RedTeam.Batch292.b292_exists_computeCoins
#print axioms Nock.RedTeam.Batch292.b292_row_counts
