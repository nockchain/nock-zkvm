/-
  Nock/RedTeam/Batch211Thm54TimestampNodupAtTierA.lean

  **`timestampPowersNodup` instantiated at `DotConfig769`, and the aggregate list measured.**

  `TraceGen/GenForestTimestampNodup.lean` fills `ExactServedMemoryTrace.timestampPowersNodup`
  (`ServedMemoryTrace.lean:610`) at the generated carrier, for any program `genComputeSkeleton`
  accepts.  A generic theorem is not done until it is instantiated at a live configuration and the
  instantiation is checked not to be thinner than its prose.

  So this module instantiates it at Tier A and **measures** rather than asserts:

  1. the aggregate list is **thirteen** field elements long, not zero and not one
     (`b211_length_eq_13`), because Tier A's eight compute rows request `3 + 2 + 1 + 1 + 3 + 1 + 1`
     `+ 1 = 13` memory records (`b211_accAt_eq_13`);
  2. those thirteen are exactly `alphaA ^ 1, …, alphaA ^ 13` up to order (`b211_perm_range`) — the
     `Nodup` is not about an unidentified list;
  3. and they are **genuinely distinct**: `b211_thirteen_distinct` states the `Nodup` of the
     explicit thirteen-element list.  `orderOf alphaA = 192` (`Batch180.alphaA_order_eq_192`) is
     what makes that true and `13 < 192` is where the orbit premise is spent — at `α` with
     `α ^ 2 = 1` the list would collapse.

  Finally `b211_partial_assembly` machine-checks that the theorem really **is** the field: it is
  `ExactServedMemoryTrace.mk` applied to `genRoots`, this batch's `Nodup`, and `forestIndexRange`,
  so its type is `(semanticCoverage : …) → ExactServedMemoryTrace …`.

  **Not claimed.**  `ExactServedMemoryTrace` is **not** inhabited at the generated carrier:
  `semanticCoverage` is still an argument of `b211_partial_assembly`, not a proof, and it is the
  one remaining field.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenForestTimestampNodup
import Nock.RedTeam.Batch196Thm54GenericRootsAtTierA

set_option autoImplicit false

namespace Nock.RedTeam.Batch211

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.Framework.Thm54

noncomputable section

/-- Tier A's table field. -/
abbrev DK := DotConfig769.K

/-- Tier A's base field. -/
abbrev DF := DotConfig769.F

/-! ## 1. The field, at Tier A

Every hypothesis is `Batch196`'s; nothing new is discharged here, because
`genRoots_timestampPowersNodup` introduces no premise `genRoots` did not already carry. -/

/-- **`ExactServedMemoryTrace.timestampPowersNodup` at the generated carrier over Tier A's
program.**  The paper's global timestamp uniqueness across the whole memory forest. -/
theorem b211_timestampPowersNodup :
    ((List.finRange Batch196.b196Cfg.kMem).flatMap
      (fun i => (Batch196.b196Roots i).timestampPowers)).Nodup :=
  genRoots_timestampPowersNodup (F := DF) seedZ alphaA 0 0 0
    (cfg seedZ alphaA).challenges Batch196.b196_hz Batch196.b196_hα
    64 executionOrbit Batch196.b196_horb (memInputs seedZ)
    (genComputeSkeleton_dot 0) Batch196.b196_horbα
    Batch196.b196_mempos Batch196.b196_comp_le Batch196.b196_mem_le

/-- **And `forestIndexRange`**, so that with `roots` three of the four fields are
available at this carrier.  `2 * 10 ≤ 64` is the compiler's choice of `Ksz`. -/
theorem b211_forestIndexRange :
    IO.InRange Batch196.b196Cfg.Ksz
      ((List.finRange Batch196.b196Cfg.kMem).flatMap
        (fun i => (Batch196.b196Roots i).timestampPowers)).length := by
  have hk : 2 * Batch196.b196Cfg.kMem ≤ 64 := by rw [Batch196.b196_kMem]; norm_num
  exact genRoots_forestIndexRange (F := DF) seedZ alphaA 0 0 0
    (cfg seedZ alphaA).challenges Batch196.b196_hz Batch196.b196_hα
    64 executionOrbit Batch196.b196_horb (memInputs seedZ)
    (genComputeSkeleton_dot 0) Batch196.b196_horbα
    Batch196.b196_mempos Batch196.b196_comp_le Batch196.b196_mem_le hk

/-! ## 2. Measured, not asserted

The
guard against the same defect here is to say what the list *is*. -/

/-- **Tier A requests thirteen memory records.**  Eight AIR-ordered compute rows, at
`recordCount` `3` (`.s6` root), `2` (`.s2`), `1` (`.s1`), `1` (`.s1`), `3` (`.s9`), `1`, `1`, `1` —
so `accAt` at the row count is `13`.  `Batch180.dot_accAt_le` only bounded this by `24`; the exact
value is what the measurement needs. -/
theorem b211_accAt_eq_13 :
    accAt (airReorder (dotTree (K := DK)))
        (bfsRows (airReorder (dotTree (K := DK)))).length = 13 := by
  rw [Batch180.dot_air_rowsLen]
  simp only [accAt, airReorder_dotTree, dot_air_bfsRows, List.getElem?_cons_zero,
    List.getElem?_cons_succ]
  simp [Nock.Framework.recordCount, dotTreeAir, dotOp2Tree, dotCondTree, dotOp1BTree,
    dotOp1CTree, dotOp9Tree, dotOp9CoreTree, dotOp9InvokeTree, skelNode, dotOp6Skel,
    dotOp2Skel, dotOp9Skel, genSkelOp1, genSkelOp2, genSkelOp6, genSkelOp9]

/-- **Thirteen timestamps in the aggregate list.**  Ten forest roots — three chained pairs and
seven single records (`assignedForest_trees`) — give `3 · 2 + 7 = 13`, and this is that count read
off the generic length theorem rather than off the fixture's forest. -/
theorem b211_length_eq_13 :
    ((List.finRange Batch196.b196Cfg.kMem).flatMap
      (fun i => (Batch196.b196Roots i).timestampPowers)).length = 13 := by
  have hl := genRoots_forestTimestampPowers_length (F := DF) seedZ alphaA 0 0 0
    (cfg seedZ alphaA).challenges Batch196.b196_hz Batch196.b196_hα
    64 executionOrbit Batch196.b196_horb (memInputs seedZ)
    (genComputeSkeleton_dot 0) Batch196.b196_horbα
    Batch196.b196_mempos Batch196.b196_comp_le Batch196.b196_mem_le
  rwa [b211_accAt_eq_13] at hl

/-- **The thirteen are `alphaA ^ 1, …, alphaA ^ 13`**, up to order.  So the `Nodup` above is a
statement about an identified list of field elements, not about an opaque one. -/
theorem b211_perm_range :
    ((List.finRange Batch196.b196Cfg.kMem).flatMap
      (fun i => (Batch196.b196Roots i).timestampPowers)).Perm
      (((List.range 13).map (fun i => i + 1)).map (fun e => alphaA ^ e)) := by
  have hp := genRoots_forestTimestampPowers_perm_range (F := DF) seedZ alphaA 0 0 0
    (cfg seedZ alphaA).challenges Batch196.b196_hz Batch196.b196_hα
    64 executionOrbit Batch196.b196_horb (memInputs seedZ)
    (genComputeSkeleton_dot 0) Batch196.b196_horbα
    Batch196.b196_mempos Batch196.b196_comp_le Batch196.b196_mem_le
  rwa [b211_accAt_eq_13] at hp

/-- **And they are genuinely distinct.**  `alphaA ^ 1, …, alphaA ^ 13` are thirteen pairwise
distinct elements of `GaloisField 769 3`.  This is where the orbit premise is spent:
`orderOf alphaA = 192` and `13 < 192`, whereas at any `α` with `α ^ 2 = 1` the list would collapse
to two values and the field would be false. -/
theorem b211_thirteen_distinct :
    (((List.range 13).map (fun i => i + 1)).map (fun e => alphaA ^ e)).Nodup :=
  b211_perm_range.nodup_iff.mp b211_timestampPowersNodup

/-! ## 3. It really is the field

`ExactServedMemoryTrace.mk` applied to three of its four arguments.

Its type is `(semanticCoverage : …) → ExactServedMemoryTrace 769 DotConfig769.Λ …`: the structure is
**not** inhabited here, and the one open field is named in the type. -/

/-- Three of `ExactServedMemoryTrace`'s four fields, at the generated carrier over Tier A's
program.  `semanticCoverage` remains an argument. -/
def b211_partial_assembly :=
  ExactServedMemoryTrace.mk (D := Batch180.dot_semanticData)
    Batch196.b196Roots b211_timestampPowersNodup b211_forestIndexRange

end

end Nock.RedTeam.Batch211

#print axioms Nock.RedTeam.Batch211.b211_timestampPowersNodup
#print axioms Nock.RedTeam.Batch211.b211_forestIndexRange
#print axioms Nock.RedTeam.Batch211.b211_accAt_eq_13
#print axioms Nock.RedTeam.Batch211.b211_length_eq_13
#print axioms Nock.RedTeam.Batch211.b211_perm_range
#print axioms Nock.RedTeam.Batch211.b211_thirteen_distinct
#print axioms Nock.RedTeam.Batch211.b211_partial_assembly
