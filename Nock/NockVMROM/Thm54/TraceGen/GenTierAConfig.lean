/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierAConfig.lean

  `ExactConfig` / `ExactExecution` for the generated Tier A OP6/OP2/OP9
  program, over base `F = ZMod 257` and table field `K = GaloisField 257 3`
  (`finrank F K = 3`).

  F97/K3 cannot host this forest: `dotMemForest_exceeds_F97_orbit` and
  `|K3*|` 2-adic valuation 5 cap the honest orbit at 32 rows.  `257` is
  prime, `256 ∣ 256 = 257-1`, and `GaloisField 257 3` therefore carries an
  element of order `2^8 = 256 ≥ 184` (`dotMemForest_unassigned_totalSize`).

  The compute tree is the generator's BFS-assigned render (8 rows).  The
  memory forest is `genMemForestFromTree` of that assigned tree: 10 roots
  and 184 nodes (`dotMemForest_assigned_length` / `_totalSize`), which
  fits the orbit `2^8 = 256`.
-/
import Nock.NockVMROM.Thm54.Execution
import Nock.NockVMROM.Thm54.ExtensionField
import Nock.NockVMROM.Thm54.TraceGen.GenTierASize
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonFanout
import Nock.NockVMROM.Thm54.ExactTraversal
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum.Prime

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig257

open Nock Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.StrictExtension

instance : Fact (Nat.Prime 257) := ⟨by norm_num⟩

abbrev F : Type := ZMod 257
abbrev K : Type := GaloisField 257 3

noncomputable abbrev φ : F →+* K := algebraMap F K
theorem φ_injective : Function.Injective φ := RingHom.injective φ

theorem two56_dvd : 256 ∣ (257 - 1 : ℕ) := by norm_num

noncomputable def omegaBase : F :=
  Classical.choose (exists_zmod_generator_of_dvd_sub_one 257 256 two56_dvd)

theorem omegaBase_order : orderOf omegaBase = 256 :=
  Classical.choose_spec (exists_zmod_generator_of_dvd_sub_one 257 256 two56_dvd)

theorem omega_order : orderOf (φ omegaBase) = 256 := by
  have h := orderOf_injective φ.toMonoidHom φ_injective omegaBase
  rw [omegaBase_order] at h
  simpa using h

theorem finrank_cubic : Module.finrank F K = 3 :=
  GaloisField.finrank 257 (by norm_num)

/-- Execution orbit of order `2^8 = 256`. -/
noncomputable def executionOrbit : OrbitDomain K where
  h := 8
  ω := φ omegaBase
  βcoset := 1
  βcoset_ne_zero := one_ne_zero
  order_ω := by simpa using omega_order

noncomputable section

def seedZ : K := φ (8 : F)
def alphaA : K := φ (4 : F)

theorem seedZ_ne_zero : seedZ ≠ 0 := by
  intro h
  have h8 : (8 : F) = 0 := φ_injective (by simpa [seedZ] using h)
  exact absurd h8 (by decide)

def computeTree (z α : K) : NTree (ComputeTable.State × ComputeTable.DTcomp K) :=
  mapNTree GenComputeRow.row (renderRows z α (bfsAssign (dotTree (K := K))))

def memoryForest (z α : K) : List (NTree (MemoryTable.MState × MemoryTable.DTmem K)) :=
  (genMemForestFromTree (encC z) z α MemoryTable.formRDefault (bfsAssign (dotTree (K := K)))).map
    (mapNTree GenMemoryRow.row)

def unassignedMemoryForest (z α : K) : List (NTree (GenMemoryRow K)) :=
  genMemForestFromTree (encC z) z α MemoryTable.formRDefault (dotTree (K := K))

/-- Shared configuration.  Memory counts are the BFS-assigned annotated
    forest. -/
noncomputable def cfg (z α : K) : ExactConfig F K where
  challenges :=
    { a := 0, b := 0, c := 0, α := α, z := z, β := 0, γ := 0, lam := MemoryTable.formRDefault }
  Ksz := 64
  kMem := 10
  orbit := executionOrbit
  orbit_h_pos := by norm_num [executionOrbit]
  compRows := 8
  memRows := 184
  compRows_pos := by norm_num
  memRows_pos := by norm_num
  compRows_le := by norm_num [executionOrbit]
  memRows_le := by norm_num [executionOrbit]
  eDeg := 1
  eDeg_eq_one := rfl
  compNodes := fun i => executionOrbit.orbitPoint i
  compNodes_spec := by intro i; rfl
  memNodes := fun i => executionOrbit.orbitPoint i
  memNodes_spec := by intro i; rfl

/-- The fixture's configured `λ` is `formRDefault`. -/
@[simp] theorem cfg_lam (z α : K) : (cfg z α).challenges.lam = MemoryTable.formRDefault := rfl

theorem computeTree_size (z α : K) : (computeTree z α).size = 8 := by
  unfold computeTree
  rw [mapNTree_size, renderRows_eq_mapNTree, mapNTree_size]
  have hsz : (bfsAssign (dotTree (K := K))).size =
      (bfsForest [bfsAssign (dotTree (K := K))]).length := by
    rw [bfsForest_length, totalSize]
    simp
  rw [hsz, bfsForest_bfsAssign, List.length_map, List.length_range']
  simp [dot_bfsForest]

theorem unassigned_kMem (z α : K) :
    (unassignedMemoryForest z α).length = 10 :=
  dotMemForest_unassigned_length z α

theorem unassigned_memRows (z α : K) :
    totalSize (unassignedMemoryForest z α) = 184 :=
  dotMemForest_unassigned_totalSize z α

theorem assigned_kMem (z α : K) :
    (genMemForestFromTree (encC z) z α MemoryTable.formRDefault (bfsAssign (dotTree (K := K)))).length = 10 :=
  dotMemForest_assigned_length z α

theorem assigned_memRows (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α MemoryTable.formRDefault (bfsAssign (dotTree (K := K)))) = 184 :=
  dotMemForest_assigned_totalSize z α

/-- Authoritative forest-first execution.  Compute rows are the BFS-assigned
    render; memory rows are the annotated forest of that same assigned tree. -/
noncomputable def exec (z α : K) : ExactExecution (cfg z α) where
  computeTree := computeTree z α
  memoryForest := memoryForest z α
  memoryForest_nonempty := by
    refine List.ne_nil_of_length_pos ?_
    unfold memoryForest
    rw [List.length_map, assigned_kMem]
    omega
  memory_root_count := by
    unfold memoryForest
    rw [List.length_map, assigned_kMem]
    simp [cfg]
  compute_bfs_length := by
    change (bfsForest [computeTree z α]).length = 8
    have := computeTree_size z α
    simpa [bfsForest_length, totalSize] using this
  memory_bfs_length := by
    change (bfsForest (memoryForest z α)).length = (cfg z α).memRows
    unfold memoryForest
    rw [bfsForest_length, totalSize_map, assigned_memRows]
    simp [cfg]

end

theorem exec_row_counts :
    (exec seedZ alphaA).computeRows.length = 8 ∧
      (exec seedZ alphaA).memoryRows.length = 184 :=
  ⟨(exec seedZ alphaA).computeRows_length, (exec seedZ alphaA).memoryRows_length⟩

end Nock.NockVMROM.Thm54.TraceGen.DotConfig257

#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig257.omega_order
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig257.finrank_cubic
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig257.exec
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig257.exec_row_counts
