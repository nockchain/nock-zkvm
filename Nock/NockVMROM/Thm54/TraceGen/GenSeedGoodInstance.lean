/-
  Nock/NockVMROM/Thm54/TraceGen/GenSeedGoodInstance.lean

  **A compiled `SeedGood` instance at a program that actually exercises the conditions.**

  A seed predicate no
  program has ever satisfied non-vacuously is untested against reality.

  This module closes that, and does so by **reusing what already existed** rather than by building a
  new witness.  `SeedOK` (`GenMatmulSeed.lean:35`) is the matmul route's own seed predicate:

      SeedOK z t := ∀ v, InTree t v →
        state ≠.s3 ∧ (state =.cons → dyck ≠ 0) ∧
        (state =.s5 → op5ResultsAgree) ∧ (state =.s5 → op5C1Ready)

  Its first three conjuncts are exactly `RowSeedGood`'s, once `state ≠.s3` is turned into
  `state =.s3 → op3CallSizeOk` by `op3CallSizeOk_of_not_s3` (`GenMatmulHyps.lean:113`).  So
  `SeedGood` follows from `SeedOK`, and `mmTree_seedOK` (`GenMatmulSeed.lean:1112`) supplies the
  instance.

  **Why the instance is non-vacuous where it matters.** `mmTree_seedOK`'s own derivation routes
  through `seedOK_gen_cons` (`:233`) and `seedOK_gen_op5` (`:123`), so the matmul tree really does
  carry `cons` and `.s5` rows and their conditions are really discharged — at `seedZ`, by the
  `AllCellDyckNe` facts decided at that seed.  This is a seed at which the `cons` Dyck condition and
  the OP5 agreement condition **hold and were checked**, not a program that dodges them.

  `SeedOK` additionally excludes `.s3` rather than discharging `op3CallSizeOk` there, so the OP3
  condition is still only met by absence.  That is stated rather than papered over: see the scope
  note on `mmTree_seedGood`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenAirTransport
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulSeed
import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.ForestExponentWindow

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

variable {K : Type} [Field K]

/-! ## `SeedGood` from `SeedOK` -/

/-- **`SeedOK` implies `SeedGood`.**

The `cons` and OP5 conjuncts transfer directly; the OP3 one comes from `SeedOK`'s `state ≠.s3`
through `op3CallSizeOk_of_not_s3`.  `SeedOK`'s fourth conjunct (`op5C1Ready`) is not needed here —
it serves `ComputeTable.WF` at `c = 1`, not `V_comp`. -/
theorem seedGood_of_seedOK {z : K} {t : NTree (GenComputeRow K)}
    (h : SeedOK z t) : SeedGood z t := by
  intro v hv
  obtain ⟨hs3, hcons, h5, _⟩ := h v hv
  exact ⟨hcons, h5, fun hst => op3CallSizeOk_of_not_s3 hs3 hst⟩

end Nock.NockVMROM.Thm54.TraceGen

/-! ## The instance

`mmTree_seedOK` and `seedZ` live in the matmul configuration's own namespace, which fixes
`F = ZMod 65537` and `K = GaloisField 65537 3`. -/

namespace Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

/-- **A compiled `SeedGood` at the 2×2 matmul program and its own seed.**

The first `SeedGood` instance in the tree, and one where the conditions are exercised rather than
absent: `mmTree_seedOK`'s derivation goes through `seedOK_gen_cons` and `seedOK_gen_op5`, so the
tree carries `cons` and `.s5` rows whose conditions are discharged at `seedZ`.

**Scope, exactly.** `SeedOK` meets the OP3 condition by **excluding** `.s3` rows, not by proving
`op3CallSizeOk` at one — so this instance does not witness that third condition being satisfied on a
row that has it. It witnesses the `cons` and OP5 conditions being genuinely met. -/
theorem mmTree_seedGood : SeedGood seedZ (mmTree (K := K)) :=
  seedGood_of_seedOK mmTree_seedOK

/-- The same at the AIR-reordered tree — the ordering a configuration would commit — by the
label transport of `DJ`. -/
theorem mmTreeAir_seedGood : SeedGood seedZ (airReorder (mmTree (K := K))) :=
  seedGood_airReorder mmTree_seedGood

/-- `V_comp` at every node of the matmul tree, from the compiled `SeedGood` — the whole chain
(`lem:ion_univariate_sec` → bounds → `SeedGood` → `V_comp`) exercised end to end at one program. -/
theorem mmTree_Vcomp_of_seedGood (α : K) (hz : (seedZ : K) ≠ 0)
    (u : NTree (GenComputeRow K)) (hu : InTree (mmTree (K := K)) u) (acc : ℕ) :
    Vcomp
      (renderNode seedZ α {(u.label) with stamp := stampOfAcc u.label.skel.state acc}).row.2.1
      (renderNode seedZ α {(u.label) with stamp := stampOfAcc u.label.skel.state acc}).row.2.2.1
      (renderNode seedZ α {(u.label) with stamp := stampOfAcc u.label.skel.state acc}).row.2.2.2 :=
  genComputeSkeleton_inTree_Vcomp_of_seedGood seedZ α hz mmTree_gen mmTree_seedGood u hu acc

end Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

#print axioms Nock.NockVMROM.Thm54.TraceGen.seedGood_of_seedOK
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.mmTree_seedGood
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.mmTreeAir_seedGood
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.mmTree_Vcomp_of_seedGood
