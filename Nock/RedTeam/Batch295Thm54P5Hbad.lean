/-
  Nock/RedTeam/Batch295Thm54P5Hbad.lean

  `hbad` of `nockCompiles_of_grom_atTree_p62` is
  `z ∉ (genSkeletonP8Census …).census.badSeeds`.  Already a failure
  event (`collisionFailureEvent = liftSeed C.badSeeds`), priced in
  `p8Work`.  Completeness,
  not a new bound summand.

  Ruled out (not implemented): `orderOf seedZ = 2^32 → hbad` (high
  order misses roots of unity but can still root a leaf/dyck
  difference); 401-row or `SepSeed` `decide` at `GaloisField`; a
  sixth §1 binder; folding `hbad` into `∃ package`; firing
  `nockCompiles` (live hyps remain: `hcoins`, `orbit`/`bas`/
  `packageOrbit`/`hcap`, `hgrom`/`hs`/`hf`, …).  `hmempos` is already
  a lemma (`mm_mempos`).  `nockCompiles_p64` staying `choose`-blocked
  is OK.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenericOffdiag
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksHbad
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksResiduals
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch295

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks
open ComputeTable

abbrev GK := MatmulConfigGoldilocks.K

/-! ## 1. Generic classification and glue. -/

theorem b295_generated_comparisons
    {K : Type} [Field K] {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hwrap : ∀ g ∈ bfsRows (airReorder t),
      g.skel.state = .s4 →
        OpcodeSemantics.incMod (ringChar K)
          (P8Census.skeletonSubformula g.skel 0 SemanticStrategy.TripleSlot.result)
          = g.skel.evaluation) :
    ∀ g ∈ bfsRows (airReorder t),
      ∀ c ∈ P8Census.skeletonComparisons (K := K) g.skel,
        c.left = c.right
        ∨ (g.skel.state = .s5 ∧ c.role = .equalityOperand)
        ∨ (g.skel.state = .s6 ∧ c.role = .recursiveFormula ∧ c.left ≠ c.right) :=
  generated_comparisons_self_or_offdiag h hwrap

theorem b295_notMem_of_offdiag
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {Λ fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (mf : List (NTree (GenMemoryRow K)))
    (hwrap : ∀ g ∈ bfsRows (airReorder t),
      g.skel.state = .s4 →
        OpcodeSemantics.incMod (ringChar K)
          (P8Census.skeletonSubformula g.skel 0 SemanticStrategy.TripleSlot.result)
          = g.skel.evaluation)
    (z : K)
    (hoff5 : ∀ g ∈ bfsRows (airReorder t), g.skel.state = .s5 →
      GlobalCarryRecognizer.SepSeed z
        (P8Census.skeletonSubformula g.skel 0 SemanticStrategy.TripleSlot.result)
        (P8Census.skeletonSubformula g.skel 1 SemanticStrategy.TripleSlot.result))
    (hoff6 : ∀ g ∈ bfsRows (airReorder t), g.skel.state = .s6 →
      GlobalCarryRecognizer.SepSeed z
        (P8Census.skeletonDec g.skel .f_tth) (P8Census.skeletonDec g.skel .f_ttt)) :
    z ∉ (genSkeletonP8Census hΛ h hconf mf).census.badSeeds :=
  notMem_badSeeds_of_offdiag_sep h hΛ hconf mf hwrap z hoff5 hoff6

/-! ## 2. `mm_hbad` is a theorem. -/

variable [Fintype GK] [DecidableEq GK]

theorem b295_hbad (hΛ : 1 ≤ (568 : ℕ)) :
    seedZ ∉ (genSkeletonP8Census (K := GK) hΛ
      (mmTree_gen (K := GK)) mm_traceConfined
      (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ)
        (mmTree (K := GK)))).census.badSeeds :=
  mm_hbad hΛ

/-! ## 3. -/

theorem b295_mempos_already :
    0 < (bfsForest (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ)
      (mmTree (K := GK)))).length :=
  mm_mempos seedZ alphaA

/-- Residual live hyps of `nockCompiles_of_grom_atTree_p62` after
`mm_hbad` and `mm_mempos`.  Not discharged in this batch. -/
def b295_nockCompiles_still_open : List String :=
  ["hcoins", "orbit/horb", "bas", "packageOrbit", "hcap",
    "hgrom", "hs", "hf", "hΛ", "hq", "hchar", "htwo",
    "hcomp", "hmem", "hwin", "hKszChar", "hprogCap", "hmemCap", "hcard"]

end Nock.RedTeam.Batch295

#print axioms Nock.RedTeam.Batch295.b295_hbad
#print axioms Nock.RedTeam.Batch295.b295_generated_comparisons
#print axioms Nock.RedTeam.Batch295.b295_notMem_of_offdiag
#print axioms Nock.RedTeam.Batch295.b295_mempos_already
