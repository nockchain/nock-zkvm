/-
  Nock/RedTeam/Batch181Thm54ServiceSupplyAtTierA.lean

  **`exists_service_of_gen_s9_lookup` instantiated at `DotConfig769` — and shown non-vacuous.**

  `TraceGen/GenServiceSupply.lean` supplies a `ServedMemoryTrace.Service` at any OP0/OP9 served
  lookup of any generated execution.

  So this module discharges **every** hypothesis at Tier A and produces an actual `Service` over
  Tier A's one genuine served lookup: the OP9 arm fetch `(dotCore, @2, dotArm)` at BFS row 6,
  timestamped `α ^ 11`.

  Three things are worth stating about the witness, because each is a way the exercise could have
  been hollow and is not:

  1. **The lookup is Tier A's own**, taken from `DotConfig769.rowData ⟨5,_⟩.needs.served` — not
     constructed here to fit.  Its `RealizesMemRec` and its recognizer `ServedLookup` are the ones
     `buildCoveredRow` produced from Tier A's skeleton.
  2. **The row is a row of the *generated* execution**, not of `DotConfig769.execThreaded`.  The two
     carriers are still different `ExactConfig`s; what makes the composition work is
     that `setRowCoins` rewrites only the input coins, so both carriers commit the *same* public row
     and hence the same `mr3`.
  3. **The axis is `2`, and nothing in the supply knew that.**  `Service.served` comes from
     `RecognizerCompleteness.servedLookup_iff_slot`, which is an equivalence at every axis — so this
     instantiation exercises the generic route, not an axis-2 special case.  That is the point of
     departure from the served-walk theory, whose `haxis : s.axis = 2` is a property of Tier A's
     program rather than of the generator.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenServiceSupply
import Nock.RedTeam.Batch167Thm54GenericCarrierAtTierA

set_option autoImplicit false

namespace Nock.RedTeam.Batch181

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.Framework.Thm54

noncomputable section

/-- Tier A's table field. -/
abbrev DK := DotConfig769.K

/-- Tier A's base field. -/
abbrev DF := DotConfig769.F

/-! ## 1. Tier A's compute tree in the shape the generic supply names

`Batch167.tierACompute` is `renderRows` of `bfsAssign dotTreeAir`; `genComputeRows` is `renderRows`
of `bfsAssign (airReorder ·)`.  `airReorder_dotTree` identifies them. -/

theorem genComputeRows_dot :
    genComputeRows seedZ alphaA (dotTree (K := DK)) = Batch167.tierACompute := by
  rw [genComputeRows, airReorder_dotTree]
  rfl

theorem b181_mempos : 0 < (bfsForest (Batch167.tierAMemory)).length :=
  Batch167.tierA_mempos

theorem b181_comp_le :
    (bfsForest [genComputeRows seedZ alphaA (dotTree (K := DK))]).length
      ≤ 2 ^ executionOrbit.h := by
  rw [genComputeRows_dot]; exact Batch167.tierA_comp_le

theorem b181_mem_le :
    (bfsForest (Batch167.tierAMemory)).length ≤ 2 ^ executionOrbit.h :=
  Batch167.tierA_mem_le

theorem b181_horb : 1 ≤ executionOrbit.h := by
  norm_num [executionOrbit]

/-- The generated carrier at Tier A's inputs.  Coins `(0,0,0)` are Tier A's own
(`GenTierAConfig769.lean:89`); they are irrelevant to everything below, since `setRowCoins` does
not touch the public row. -/
def b181Exec :
    ExactExecution (genExactConfig (F := DF) (cfg seedZ alphaA).challenges 64
      executionOrbit b181_horb (genComputeRows seedZ alphaA (dotTree (K := DK)))
      Batch167.tierAMemory b181_mempos b181_comp_le b181_mem_le) :=
  genExactExecution (F := DF) (cfg seedZ alphaA).challenges 64 executionOrbit b181_horb
    0 0 0 (genComputeRows seedZ alphaA (dotTree (K := DK))) Batch167.tierAMemory
    b181_mempos b181_comp_le b181_mem_le

def b181ExecA :
    ExactExecution (genExactConfig (F := DF) (cfg seedZ alphaA).challenges 64
      executionOrbit b181_horb (genComputeRows seedZ alphaA (dotTree (K := DK)))
      Batch167.tierAMemory b181_mempos b181_comp_le b181_mem_le) :=
  genExactExecutionA (F := DF) (cfg seedZ alphaA).challenges 64 executionOrbit b181_horb
    0 0 0 (genComputeRows seedZ alphaA (dotTree (K := DK))) Batch167.tierAMemory
    b181_mempos b181_comp_le b181_mem_le

/-! ## 2. The OP9 row of the generated execution -/

/-- Tier A's OP9 node, BFS row 6 of the AIR-ordered tree. -/
def b181Node : GenComputeRow DK :=
  bfsLabelAt (dotTreeAir (K := DK)) 6

/-- The public compute row the generated execution commits at that node. -/
def b181Row : ComputeTable.State × ComputeTable.DTcomp DK :=
  setRowCoins 0 0 0 (renderNode seedZ alphaA b181Node).row

theorem b181Node_mem : b181Node ∈ bfsRows (bfsAssign (dotTreeAir (K := DK))) := by
  have h : bfsRows (bfsAssign (dotTreeAir (K := DK))) =
      (List.range' 1 (bfsForest [dotTreeAir (K := DK)]).length).map
        (bfsLabelAt (dotTreeAir (K := DK))) := bfsAssign_bfsForest_labels _
  rw [h]
  refine List.mem_map.mpr ⟨6, ?_, rfl⟩
  have hlen : (bfsForest [dotTreeAir (K := DK)]).length = 8 := by
    rw [← bfsRows_length, dot_air_bfsRows]
    rfl
  rw [hlen]
  decide

theorem b181Row_mem : b181Row ∈ b181Exec.computeRows := by
  rw [b181Exec, genExactExecution_computeRows, genComputeRows, airReorder_dotTree,
    show renderRows seedZ alphaA (bfsAssign (dotTreeAir (K := DK)))
      = renderRows seedZ alphaA (bfsAssign (dotTreeAir (K := DK))) from rfl]
  refine List.mem_map.mpr ⟨renderNode seedZ alphaA b181Node, ?_, rfl⟩
  rw [bfsRows_renderRows]
  exact List.mem_map.mpr ⟨b181Node, b181Node_mem, rfl⟩

theorem b181Row_state : b181Row.2.2.1.state = .s9 := by
  show (renderNode seedZ alphaA b181Node).row.2.2.1.state = .s9
  rw [renderNode_pub_state]
  exact air_row_s9

/-- The generated execution's OP9 row commits the **same** served record as
`DotConfig769.execThreaded` does: `setRowCoins` rewrites only the inputs. -/
theorem b181Row_mr3 :
    computeMemRec b181Row.2.2.1 2 = recOf seedZ alphaA dotCore dotArm 2 11 := by
  have h := computeRowAt_five_mr3
  rw [computeRowAt_eq_threaded] at h
  exact h

/-! ## 3. Tier A's served lookup

`rowData_five_servedTuples` (`GenTierAMemoryTrace.lean:1723`) says row 5's served list has exactly
one tuple.  This extracts the lookup itself. -/

/-- Tier A's OP9 row index. -/
def b181Idx : Fin (cfg seedZ alphaA).compRows := ⟨5, by simp [cfg]⟩

theorem b181_lookup_exists :
    ∃ l ∈ (rowData b181Idx).needs.served,
      lookupTuple l = (recOf seedZ alphaA dotCore dotArm 2 11, dotCore, 2, dotArm) := by
  have hmem : (recOf seedZ alphaA dotCore dotArm 2 11, dotCore, (2 : ℕ), dotArm) ∈
      (rowData b181Idx).needs.served.map lookupTuple := by
    rw [show b181Idx = ⟨5, by simp [cfg]⟩ from rfl, rowData_five_servedTuples]
    simp
  obtain ⟨l, hl, hlt⟩ := List.mem_map.mp hmem
  exact ⟨l, hl, hlt⟩

/-- Tier A's row-5 seed is the configuration's, so the lookup lives at the generated carrier's
`z` too.  `renderNode` writes `⟨α, z, 0, 0, 0⟩` into every rendered row (`GenTierAAccept.lean:36`). -/
theorem b181_row_z :
    ((execThreaded seedZ alphaA).computeRowAt b181Idx).2.1.z =
      (genExactConfig (F := DF) (cfg seedZ alphaA).challenges 64 executionOrbit b181_horb
        (genComputeRows seedZ alphaA (dotTree (K := DK))) Batch167.tierAMemory
        b181_mempos b181_comp_le b181_mem_le).challenges.z := by
  rw [computeRowAt_eq_threaded, renderNode_inputs]
  rfl

/-- Transporting a lookup along an equality of seeds leaves its four coordinates alone. -/
private theorem lookup_cast {z₁ z₂ : DK} (h : z₁ = z₂) (l : ServedNounLookup z₁) :
    (h ▸ l : ServedNounLookup z₂).record = l.record ∧
      (h ▸ l : ServedNounLookup z₂).root = l.root ∧
        (h ▸ l : ServedNounLookup z₂).axis = l.axis ∧
          (h ▸ l : ServedNounLookup z₂).child = l.child := by
  subst h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## 4. The service

Every hypothesis of `exists_service_of_gen_s9_lookup` is now in hand. -/

/-- **A `Service` over Tier A's OP9 arm fetch, on the generated carrier.**

The four conjuncts are exactly the four `ExactServedMemoryTrace.semanticCoverage` compares.  The
lookup is Tier A's own — `rowData`'s, produced by `buildCoveredRow` — and the axis is `2`, which no
hypothesis of the supply mentions. -/
theorem b181_service_exists :
    ∃ (l : ServedNounLookup
        (genExactConfig (F := DF) (cfg seedZ alphaA).challenges 64 executionOrbit b181_horb
          (genComputeRows seedZ alphaA (dotTree (K := DK))) Batch167.tierAMemory
          b181_mempos b181_comp_le b181_mem_le).challenges.z)
      (s : ServedMemoryTrace.Service _ b181ExecA),
      l.record = recOf seedZ alphaA dotCore dotArm 2 11 ∧
        l.root = dotCore ∧ l.axis = 2 ∧ l.child = dotArm ∧
        s.record = l.record ∧ s.root = l.root ∧ s.child = l.child ∧ s.axis = l.axis := by
  obtain ⟨l0, _, hl0⟩ := b181_lookup_exists
  refine ⟨b181_row_z ▸ l0, ?_⟩
  obtain ⟨hrec, hroot, haxis, hchild⟩ := lookup_cast b181_row_z l0
  have h1 : l0.record = recOf seedZ alphaA dotCore dotArm 2 11 := congrArg Prod.fst hl0
  have h2 : l0.root = dotCore := congrArg (fun p => p.2.1) hl0
  have h3 : l0.axis = 2 := congrArg (fun p => p.2.2.1) hl0
  have h4 : l0.child = dotArm := congrArg (fun p => p.2.2.2) hl0
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ :=
    exists_service_of_gen_s9_lookup (F := DF) seedZ alphaA 0 0 0
      (cfg seedZ alphaA).challenges rfl 64 executionOrbit b181_horb
      (dotTree (K := DK)) Batch167.tierAMemory b181_mempos b181_comp_le b181_mem_le
      b181Row b181Row_mem b181Row_state (b181_row_z ▸ l0)
      (by rw [hrec, h1, ← b181Row_mr3])
  exact ⟨s, by rw [hrec, h1], by rw [hroot, h2], by rw [haxis, h3], by rw [hchild, h4],
    hs1, hs2, hs3, hs4⟩

/-! ## 5. The same service, through the `semanticCoverage` interface

`exists_service_of_servedTuple` is the form lane 3 will call: it takes membership in
`BoundSemanticTrace.servedTuplesOf` — which is what `buildCoveredRow` hands out about a row's served
lookups — and does the OP0/OP9 split itself.  Exercising it here means the instantiation tests the
theorem that will actually be composed, not only the record-slot form beneath it. -/

/-- The generated row and `DotConfig769.execThreaded`'s row commit the **same** public columns:
`setRowCoins` rewrites only the inputs. -/
theorem b181Row_pub :
    b181Row.2.2.1 = ((execThreaded seedZ alphaA).computeRowAt b181Idx).2.2.1 := by
  rw [computeRowAt_eq_threaded]
  rfl

/-- Tier A's row-5 skeleton is the OP9 one, so the generated row's state matches it. -/
theorem b181Row_skel_state :
    b181Row.2.2.1.state =
      (BoundSemanticTrace.skeletonRowAt (semanticSkeleton seedZ alphaA)
        (execThreaded seedZ alphaA) bindsAt_seed b181Idx).state := by
  rw [b181Row_state, show b181Idx = ⟨5, by simp [cfg]⟩ from rfl, skelAt_five]
  rfl

/-- **The service again, via the interface `semanticCoverage` will use.** -/
theorem b181_service_via_tuple :
    ∃ (l : ServedNounLookup
        (genExactConfig (F := DF) (cfg seedZ alphaA).challenges 64 executionOrbit b181_horb
          (genComputeRows seedZ alphaA (dotTree (K := DK))) Batch167.tierAMemory
          b181_mempos b181_comp_le b181_mem_le).challenges.z)
      (s : ServedMemoryTrace.Service _ b181ExecA),
      l.axis = 2 ∧
        s.record = l.record ∧ s.root = l.root ∧ s.child = l.child ∧ s.axis = l.axis := by
  obtain ⟨l0, hl0mem, hl0⟩ := b181_lookup_exists
  obtain ⟨hrec, hroot, haxis, hchild⟩ := lookup_cast b181_row_z l0
  have hmap : lookupTuple l0 ∈
      BoundSemanticTrace.servedTuplesOf
        (BoundSemanticTrace.skeletonRowAt (semanticSkeleton seedZ alphaA)
          (execThreaded seedZ alphaA) bindsAt_seed b181Idx)
        ((execThreaded seedZ alphaA).computeRowAt b181Idx).2.2.1 := by
    rw [← rowData_servedTuples b181Idx]
    exact List.mem_map.mpr ⟨l0, hl0mem, rfl⟩
  refine ⟨b181_row_z ▸ l0, ?_⟩
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ :=
    exists_service_of_servedTuple (F := DF) seedZ alphaA 0 0 0
      (cfg seedZ alphaA).challenges rfl 64 executionOrbit b181_horb
      (dotTree (K := DK)) Batch167.tierAMemory b181_mempos b181_comp_le b181_mem_le
      b181Row b181Row_mem _ b181Row_skel_state (b181_row_z ▸ l0)
      (by rw [hrec, hroot, haxis, hchild, b181Row_pub]; exact hmap)
  exact ⟨s, by rw [haxis]; exact congrArg (fun p => p.2.2.1) hl0, hs1, hs2, hs3, hs4⟩

end

end Nock.RedTeam.Batch181

#print axioms Nock.RedTeam.Batch181.b181Row_mem
#print axioms Nock.RedTeam.Batch181.b181Row_state
#print axioms Nock.RedTeam.Batch181.b181Row_mr3
#print axioms Nock.RedTeam.Batch181.b181_lookup_exists
#print axioms Nock.RedTeam.Batch181.b181_service_exists
#print axioms Nock.RedTeam.Batch181.b181Row_pub
#print axioms Nock.RedTeam.Batch181.b181_service_via_tuple
