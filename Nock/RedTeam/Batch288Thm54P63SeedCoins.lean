/-
  Nock/RedTeam/Batch288Thm54P63SeedCoins.lean

  `exists_computeCoinsGeneric_airReorder` (`GenCoinCounting.lean`) produces a
  good coin triple as soon as the compute-row count is below `|K|`.  At
  `DotConfig769` that is `8 < 769³`, and the chosen coins inhabit
  `nockCompiles_of_grom_atTree_p62`.  No new failure event or summand: the
  counted set is the existing `computeCoinFailure`.

  **`hseed` is not claimed.**  The witness
  still uses `Batch180.dot_seedGood` (vacuous at Tier A).  `GoodSeed.nockCompiles_p63`
  is the same coin discharge at `romSeed` and is not instantiated here (`P6.4`).
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.RedTeam.Batch286Thm54P62CapacityBinders
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Nock.RedTeam.Batch288

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.Framework.Thm54
open Nock.RedTeam

abbrev DK := DotConfig769.K
abbrev DF := DotConfig769.F

local instance charRingDK : CharP DK (ringChar DK) := ringChar.charP DK

noncomputable section




/-- The `GS` side condition at Tier A: eight compute rows sit below `|K| = 769³`. -/
theorem b288_rows_lt_card :
    (bfsForest [airReorder (dotTree (K := DK))]).length < Fintype.card DK := by
  rw [← bfsRows_length, Batch180.dot_air_rowsLen, DotConfig769.card_K]
  norm_num

/-- Good compute coins exist at Tier A's tree, from the existing counted event. -/
theorem b288_exists_computeCoins :
    ∃ a b c : DK, ComputeCoinsGeneric seedZ alphaA a b c
      (airReorder (dotTree (K := DK))) :=
  exists_computeCoinsGeneric_airReorder seedZ alphaA (dotTree (K := DK))
    b288_rows_lt_card

/-- **`nockCompiles_of_grom_atTree_p62` at Tier A with compiler-chosen coins.**
Same program as `Batch286.b286_nockCompiles_p62`; the caller no longer supplies
`a`, `b`, `c` or `hcoins`.  `hseed` is still supplied (`dot_seedGood`). -/
noncomputable def b288_nockCompiles_p63 :=
  let a := Classical.choose b288_exists_computeCoins
  let hb := Classical.choose_spec b288_exists_computeCoins
  let b := Classical.choose hb
  let hc := Classical.choose_spec hb
  let c := Classical.choose hc
  let hcoins := Classical.choose_spec hc
  nockCompiles_of_grom_atTree_p62 (F := DF) (q := 769) (Λ := DotConfig769.Λ)
    seedZ alphaA alphaA MemoryTable.formRDefault seedZ_ne_zero two_ne_zero a b c
    DotConfig769.executionOrbit Batch216.b216_horb (genComputeSkeleton_dot 0)
    Batch263.b263_subject_bounded Batch263.b263_formula_bounded Batch263.b263_grom
    (Batch180.dot_seedGood _) hcoins
    (by norm_num [DotConfig769.Λ]) Batch180.dot_air_traceConfined
    Batch216.b216_comp_le Batch216.b216_mem_le
    Batch286.b286_hwin Batch285.b285_dot_hmemOrd
    (by norm_num) DotConfig769.ringChar_K.symm
    Batch180.dot_hlt
    (Batch180.not_mem_badSeeds_of_pairs _ _ Batch180.dot_gen_pairs_sep)
    Batch180.dot_gen_hout
    Batch286.b286_hKszChar Batch221.b221_hprogCap Batch221.b221_hmemCap
    DotConfig769.basis DotConfig769.strictOrbit Batch251.b251_hcap
    Batch286.b286_hcard
    Batch285.b285_dot_hrows DotConfig769.dot_primeField Batch221.b221_laterSeedZeros

end

end Nock.RedTeam.Batch288

#print axioms Nock.RedTeam.Batch288.b288_rows_lt_card
#print axioms Nock.RedTeam.Batch288.b288_exists_computeCoins
#print axioms Nock.RedTeam.Batch288.b288_nockCompiles_p63
