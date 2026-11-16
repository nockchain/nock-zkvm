/-
  Nock/RedTeam/Batch216Thm54SemanticCoverageAtTierA.lean

  **`semanticCoverage` instantiated at `DotConfig769`, and measured.**

  `TraceGen/GenServedSemanticCoverage.lean` fills `ExactServedMemoryTrace.semanticCoverage`
  (`ServedMemoryTrace.lean:616`) at the generated carrier: every served lookup of every compute row
  of `genSemanticData`'s rows is matched, on record/root/child/axis, by a `Service` that is a
  **member** of some `genRoots` root's `services` list.  This module discharges every hypothesis of
  that theorem at Tier A (`GaloisField 769 3`, seed `φ(8)`, `α = φ(4)`, coins `(0,0,0)`,
  `Ksz = 64`, `Λ = 22`) by reusing `Batch180`'s discharges verbatim, and then measures how much the
  instantiation actually exercises.

  **The measurement is thin, and saying so is the point.**  Tier A's eight compute rows carry
  states `s6, s2, s1, s1, s1, s9, s1, s1`.  `servedTuplesOf` is `[]` at nine of the eleven states
  and a singleton at `.s0` and `.s9`, so **exactly one** row — index `5`, the OP9 row — carries a
  served lookup, and it carries exactly one.  `b216_served_nil` and `b216_served_length_five` are
  that, proved rather than asserted.

  So this entry witnesses the generic theorem at **one lookup**.  It is a non-vacuity check: the
  coverage obligation is not discharged by an empty quantifier at this configuration, and the
  `Service` it produces really is drawn from a root's `services` list.  It is **not** evidence
  about a family of lookups, about the chained-root arm of the supply, or about the `.s0` arm at
  all — Tier A has no OP0 row.  The generic theorem covers all eleven states and both root shapes;
  this instantiation exercises one state and whichever shape root `5`'s record lands in.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenServedSemanticCoverage
import Nock.RedTeam.Batch180Thm54GenericSemanticDataAtTierA
import Nock.RedTeam.Batch196Thm54GenericRootsAtTierA

set_option autoImplicit false

namespace Nock.RedTeam.Batch216

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.BoundSemanticTrace
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.Framework.Thm54

/-- Tier A's table field. -/
abbrev DK := DotConfig769.K

/-- Tier A's base field. -/
abbrev DF := DotConfig769.F

/-! ## The two noncomputable instances the counted-seed formulation forces

Identical to `Batch180`'s, and `local` for the same reason: instance search finds neither
`Fintype` nor `DecidableEq` at `GaloisField 769 3`. -/

noncomputable local instance : Fintype DK := Fintype.ofFinite _
noncomputable local instance : DecidableEq DK := Classical.decEq _

noncomputable section

/-! ## 1. The generated carrier at Tier A -/

abbrev b216Chal : ChallengeVector DK := (cfg seedZ alphaA).challenges

theorem b216_horb : 1 ≤ executionOrbit.h := by
  norm_num [executionOrbit]

theorem b216_mempos :
    0 < (bfsForest (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))).length := by
  rw [Batch180.dot_memRowsLen]; norm_num

theorem b216_comp_le :
    (bfsForest [genComputeRows seedZ alphaA (dotTree (K := DK))]).length
      ≤ 2 ^ executionOrbit.h := by
  rw [Batch180.dot_compRowsLen]; norm_num [executionOrbit]

theorem b216_mem_le :
    (bfsForest (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))).length
      ≤ 2 ^ executionOrbit.h := by
  rw [Batch180.dot_memRowsLen]; norm_num [executionOrbit]

theorem b216_hzc : b216Chal.z = seedZ := rfl

theorem b216_hαc : b216Chal.α = alphaA := rfl

/-- **The orbit-capacity premise, met** — `accAt ≤ 24 < 192 = orderOf alphaA`.  Identical to
`Batch196`'s, restated here so this module's `genRoots` is the same term. -/
theorem b216_horbα :
    accAt (airReorder (dotTree (K := DK)))
        (bfsRows (airReorder (dotTree (K := DK)))).length < orderOf alphaA := by
  refine lt_of_le_of_lt Batch180.dot_accAt_le ?_
  rw [Batch180.alphaA_order_eq_192]
  norm_num

def b216Cfg : ExactConfig DF DK :=
  genExactConfig (F := DF) b216Chal 64 executionOrbit b216_horb
    (genComputeRows seedZ alphaA (dotTree (K := DK)))
    (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))
    b216_mempos b216_comp_le b216_mem_le

def b216Exec : ExactExecution b216Cfg :=
  genExactExecution (F := DF) b216Chal 64 executionOrbit b216_horb 0 0 0
    (genComputeRows seedZ alphaA (dotTree (K := DK)))
    (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))
    b216_mempos b216_comp_le b216_mem_le

def b216ExecA : ExactExecution b216Cfg :=
  genExactExecutionA (F := DF) b216Chal 64 executionOrbit b216_horb 0 0 0
    (genComputeRows seedZ alphaA (dotTree (K := DK)))
    (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))
    b216_mempos b216_comp_le b216_mem_le

/-- Tier A's generic semantic data, `Batch180`'s object with this module's argument spelling. -/
def b216Data
     :
    SemanticTrace.ExactExecutionSemanticData 769 DotConfig769.Λ b216Cfg b216Exec :=
  genSemanticData (F := DF) seedZ alphaA seedZ_ne_zero two_ne_zero 0 0 0 b216Chal
    Batch180.dot_hinp (DotConfig769.memoryInputs_eq _ _)
    64 executionOrbit b216_horb (genComputeSkeleton_dot 0)
    (Batch180.dot_seedGood _) (Batch180.dot_computeCoins _ _ _ _ _)
    (by norm_num [DotConfig769.Λ]) Batch180.dot_air_traceConfined
    b216_mempos b216_comp_le b216_mem_le
    192 (le_of_eq Batch180.alphaA_order_eq_192.symm)
    (by have := Batch180.dot_accAt_le; omega)
    (by have := Batch180.dot_accAt_le; omega)
    Batch180.dot_hb (by norm_num) DotConfig769.ringChar_K.symm Batch180.dot_haxis
    (Batch180.not_mem_badSeeds_of_pairs _ _ Batch180.dot_gen_pairs_sep)
    Batch180.dot_gen_hout Batch180.dot_hlt

/-- `roots`, at Tier A — the same construction `Batch196` measured. -/
def b216Roots : ∀ i : Fin b216Cfg.kMem, RootTrace b216Cfg b216ExecA i :=
  genRoots (F := DF) seedZ alphaA 0 0 0 b216Chal b216_hzc b216_hαc 64 executionOrbit b216_horb
    (memInputs seedZ) (genComputeSkeleton_dot 0) b216_horbα
    b216_mempos b216_comp_le b216_mem_le

/-! ## 2. `semanticCoverage`, discharged at Tier A

Every hypothesis of `genSemanticData_semanticCoverage` is supplied; nothing is assumed. -/

/-- **`ExactServedMemoryTrace.semanticCoverage` at `DotConfig769`'s generated carrier.**

Read against the field (`ServedMemoryTrace.lean:616`) this is that type verbatim, with
`D := b216Data` and `roots := b216Roots`. -/
theorem b216_semanticCoverage
     :
    ∀ row : Fin b216Cfg.compRows,
      ∀ lookup ∈ ((b216Data).rows row).needs.served,
        ∃ (i : Fin b216Cfg.kMem) (s : Service b216Cfg b216ExecA),
          s ∈ (b216Roots i).services ∧
            s.record = lookup.record ∧ s.root = lookup.root ∧
              s.child = lookup.child ∧ s.axis = lookup.axis :=
  genSemanticData_semanticCoverage (F := DF) seedZ alphaA seedZ_ne_zero two_ne_zero 0 0 0
    b216Chal Batch180.dot_hinp (DotConfig769.memoryInputs_eq _ _)
    64 executionOrbit b216_horb (genComputeSkeleton_dot 0)
    (Batch180.dot_seedGood _) (Batch180.dot_computeCoins _ _ _ _ _)
    (by norm_num [DotConfig769.Λ]) Batch180.dot_air_traceConfined
    b216_mempos b216_comp_le b216_mem_le
    192 (le_of_eq Batch180.alphaA_order_eq_192.symm)
    (by have := Batch180.dot_accAt_le; omega)
    (by have := Batch180.dot_accAt_le; omega)
    Batch180.dot_hb (by norm_num) DotConfig769.ringChar_K.symm Batch180.dot_haxis
    Batch180.dot_hlt
    (Batch180.not_mem_badSeeds_of_pairs _ _ Batch180.dot_gen_pairs_sep)
    Batch180.dot_gen_hout

/-! ## 3. How thin the instantiation is — measured, not asserted

`ES.2` is this file's record of counted conditions that excluded nothing.  The dual risk here is a
coverage obligation discharged by an empty quantifier, so the served-lookup count is computed. -/

/-- Tier A's generic semantic skeleton, named. -/
abbrev b216Skel : SemanticSkeleton :=
  genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK))))
    (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))

theorem b216Binds : BindsAt seedZ b216Skel b216Cfg b216Exec :=
  genBindsAt_threaded (F := DF) seedZ alphaA (memInputs seedZ) b216Chal b216_hzc
    64 executionOrbit b216_horb 0 0 0 (genComputeSkeleton_dot 0)
    b216_mempos b216_comp_le b216_mem_le

/-- The eight states, as a list literal. -/
abbrev b216States : List ComputeTable.State :=
  [.s6, .s2, .s1, .s1, .s1, .s9, .s1, .s1]

/-- **Tier A's eight row states.**  `dot_genSkeleton` identifies the generic skeleton with Tier A's
own, and `semanticSkeleton_computeRows` lists its rows. -/
theorem b216_skel_states :
    (computeSkeletonRows b216Skel).map (fun s => s.state) = b216States := by
  show (computeSkeletonRows (genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK))))
      (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK))))).map
      (fun s => s.state) = _
  rw [Batch180.dot_genSkeleton, semanticSkeleton_computeRows]
  rfl

theorem b216_compRows : b216Cfg.compRows = 8 :=
  Batch180.dot_compRowsLen

theorem b216_skelRows_length : (computeSkeletonRows b216Skel).length = 8 := by
  have h := congrArg List.length b216_skel_states
  rw [List.length_map] at h
  exact h

/-- The state at row `row`, read off the eight-element list. -/
theorem b216_rowState (row : Fin b216Cfg.compRows) :
    (b216Exec.computeRowAt row).1
      = b216States[(row : ℕ)]'
          (by simpa using (show (row : ℕ) < 8 from by rw [← b216_compRows]; exact row.isLt)) := by
  have hbind := skeletonRowAt_binds b216Skel b216Exec b216Binds row
  have h8 : (row : ℕ) < 8 := by rw [← b216_compRows]; exact row.isLt
  have hlt : (row : ℕ) < (computeSkeletonRows b216Skel).length := by
    rw [b216_skelRows_length]; exact h8
  have hmaplt : (row : ℕ) < ((computeSkeletonRows b216Skel).map
      (fun s => s.state)).length := by rw [List.length_map]; exact hlt
  have hstep := List.getElem_of_eq b216_skel_states hmaplt
  rw [List.getElem_map] at hstep
  refine hbind.1.trans ?_
  refine Eq.trans ?_ hstep
  show ((computeSkeletonRows b216Skel).get _).state = _
  rw [List.get_eq_getElem]
  rfl

/-- The served-lookup count at each row, from `RowStateNeeds.served_count`. -/
theorem b216_served_length
    (row : Fin b216Cfg.compRows) :
    ((b216Data).rows row).needs.served.length
      = SemanticTrace.requiredServedLookups ((b216Exec.computeRowAt row).1) :=
  ((b216Data).rows row).needs.served_count

private theorem b216_states_required_zero (k : ℕ) (hk : k < 8) (h5 : k ≠ 5) :
    SemanticTrace.requiredServedLookups (b216States[k]'hk) = 0 := by
  interval_cases k <;> simp_all [SemanticTrace.requiredServedLookups]

/-- **Seven of the eight rows carry no served lookup at all.** -/
theorem b216_served_nil
    (row : Fin b216Cfg.compRows) (h5 : (row : ℕ) ≠ 5) :
    ((b216Data).rows row).needs.served = [] := by
  refine List.eq_nil_of_length_eq_zero ?_
  rw [b216_served_length row, b216_rowState row]
  exact b216_states_required_zero (row : ℕ) _ h5

/-- **The OP9 row carries exactly one.**  So the whole trace has one served lookup, and
`b216_semanticCoverage` is a statement about that one — not about a family. -/
theorem b216_served_length_five
    (h : (5 : ℕ) < b216Cfg.compRows) :
    ((b216Data).rows ⟨5, h⟩).needs.served.length = 1 := by
  rw [b216_served_length ⟨5, h⟩, b216_rowState ⟨5, h⟩]
  rfl

end

end Nock.RedTeam.Batch216

#print axioms Nock.RedTeam.Batch216.b216_horbα
#print axioms Nock.RedTeam.Batch216.b216Roots
#print axioms Nock.RedTeam.Batch216.b216_semanticCoverage
#print axioms Nock.RedTeam.Batch216.b216_skel_states
#print axioms Nock.RedTeam.Batch216.b216_rowState
#print axioms Nock.RedTeam.Batch216.b216_served_nil
#print axioms Nock.RedTeam.Batch216.b216_served_length_five
