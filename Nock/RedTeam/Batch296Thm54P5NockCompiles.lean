/-
  Nock/RedTeam/Batch296Thm54P5NockCompiles.lean

  No new theory,
  no new `∀` binder, no new failure-event summand, no `nockCompiles_p64`
  (`romSeedVcomp` stays `Classical.choose`).  Not the §1 `∀ program`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulBounded
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulConfigGoldilocks
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksHbad
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksResiduals
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksSeed
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulTraceConfined
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Nock.RedTeam.Batch296

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks
open Nock.Framework.Thm54

abbrev GF := MatmulConfigGoldilocks.F
abbrev GK := MatmulConfigGoldilocks.K

local instance charRingGK : CharP GK (ringChar GK) := ringChar.charP GK

noncomputable local instance : Fintype GK := Fintype.ofFinite _
noncomputable local instance : DecidableEq GK := Classical.decEq _

noncomputable section

/-- Program-text window used by `mm_traceConfined` / `mm_hbad` / `mm_hout`. -/
noncomputable def b296_hΛ : 1 ≤ (568 : ℕ) := by decide

/-- Real evaluator result: `[[2 1] [1 1]]`. -/
noncomputable def b296_claimed_is_mmC : mmC =
    .cell (.cell (.atom 2) (.atom 1)) (.cell (.atom 1) (.atom 1)) :=
  rfl

noncomputable def b296_evalN : Nock.evalN 64 mmSubject mmFormula = some mmC :=
  mm_evalN (K := GK)

theorem b296_hrows :
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

/-- **`nockCompiles_of_grom_atTree_p62` at the Goldilocks 2×2 matmul.**
    Literal `seedZ`; coins inhabited from `mm_exists_computeCoins`.
    Claim is the program triple; `mmC` is `evalN`'s result. -/
noncomputable def b296_nockCompiles_literal :=
  let a := Classical.choose mm_exists_computeCoins
  let ha := Classical.choose_spec mm_exists_computeCoins
  let b := Classical.choose ha
  let hb := Classical.choose_spec ha
  let c := Classical.choose hb
  let hcoins := Classical.choose_spec hb
  fun hfirst hmore =>
    nockCompiles_of_grom_atTree_p62 (hF := GeneratedField.primeFieldElems_zmod _) (hrows := b296_hrows) (F := GF) (q := Field.p) (Λ := 568)
      seedZ alphaA alphaA MemoryTable.formRDefault seedZ_ne_zero two_ne_zero a b c
      executionOrbit horb (mmTree_gen (K := GK))
      mmSubject_bounded_p mmFormula_bounded_p mm_grom
      mmTree_seedGood hcoins
      b296_hΛ mm_traceConfined
      (mm_hcomp seedZ alphaA) (mm_hmem seedZ alphaA)
      mm_hwin mm_hmemOrd
      hq hchar
      hfirst (mm_hbad b296_hΛ) mm_hout
      (by rw [← compilerKszOf_eq_L]; exact mm_hKszChar seedZ alphaA) mm_hprogCap
      (by rw [← programMemRows_eq_L]; exact mm_hmemCap seedZ alphaA)
      basis packageOrbit hcap
      (by rw [← compilerNOf_eq_L]; exact mm_hcard seedZ alphaA) hmore

end

end Nock.RedTeam.Batch296

#print axioms Nock.RedTeam.Batch296.b296_nockCompiles_literal
#print axioms Nock.RedTeam.Batch296.b296_evalN
#print axioms Nock.RedTeam.Batch296.b296_claimed_is_mmC
