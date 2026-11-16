/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulConfig.lean

  `ExactConfig` for the generated 2×2 matmul program, over base
  `F = ZMod 65537` and table field `K = GaloisField 65537 3`
  (`finrank F K = 3`).

  The assigned memory forest has 618 roots / 30936 rows, which exceeds
  F97's orbit cap `2^5 = 32` and the Tier A 257 orbit `2^8 = 256`.
  Fermat prime `65537 = 2^16 + 1` supplies an element of order `2^16 = 65536`
  (`exists_zmod_generator_of_dvd_sub_one`), which hosts both the 401-row
  compute tree (`mmTree_size`) and the 30936-row memory forest.

  The OP1-slice sample `α = φ(4)` has order `16` in `ZMod 65537`, which
  cannot separate the 401-row request schedule.  The inhabitant `α` is
  therefore the same generator of order `2^16` that hosts the orbit.

  Assigned forest counts 618 / 30936 are `mmMemForest_assigned_*`, obtained
  by transporting the unassigned constructor-walk totals through `bfsAssign`
  (stamp-independent row forests).  Every assigned memory tree inhabits
  `MemoryNodesOK` (`mmMemForest_OK`).  `ExactExecution` is the forest-first
  carrier: assigned compute tree, assigned memory forest, root count, and
  the two BFS lengths.
-/
import Nock.NockVMROM.Thm54.Execution
import Nock.NockVMROM.Thm54.ExtensionField
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulSize
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulData
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulMemSize
import Nock.NockVMROM.Thm54.TraceGen.GenWF
import Nock.NockVMROM.Thm54.ExactTraversal
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum.Prime

namespace Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

open Nock Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.StrictExtension

instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

abbrev F : Type := ZMod 65537
abbrev K : Type := GaloisField 65537 3

noncomputable abbrev φ : F →+* K := algebraMap F K
theorem φ_injective : Function.Injective φ := RingHom.injective φ

theorem two16_dvd : 65536 ∣ (65537 - 1 : ℕ) := by norm_num

noncomputable def omegaBase : F :=
  Classical.choose (exists_zmod_generator_of_dvd_sub_one 65537 65536 two16_dvd)

theorem omegaBase_order : orderOf omegaBase = 65536 :=
  Classical.choose_spec (exists_zmod_generator_of_dvd_sub_one 65537 65536 two16_dvd)

theorem omega_order : orderOf (φ omegaBase) = 65536 := by
  have h := orderOf_injective φ.toMonoidHom φ_injective omegaBase
  rw [omegaBase_order] at h
  simpa using h

theorem finrank_cubic : Module.finrank F K = 3 :=
  GaloisField.finrank 65537 (by norm_num)

/-- Execution orbit of order `2^16 = 65536`. -/
noncomputable def executionOrbit : OrbitDomain K where
  h := 16
  ω := φ omegaBase
  βcoset := 1
  βcoset_ne_zero := one_ne_zero
  order_ω := by simpa using omega_order

noncomputable section

def seedZ : K := φ (8 : F)
/-- Honest `α` is the orbit generator (`orderOf = 2^16`).  `φ(4)` has
    order `16` and cannot inhabit `requestNodup`. -/
def alphaA : K := φ omegaBase

theorem seedZ_ne_zero : seedZ ≠ 0 := by
  intro h
  have h8 : (8 : F) = 0 := φ_injective (by simpa [seedZ] using h)
  exact absurd h8 (by decide)

theorem alphaA_order : orderOf alphaA = 65536 :=
  omega_order

theorem alphaA_ne_zero : alphaA ≠ 0 := by
  intro h
  have hpow := pow_orderOf_eq_one alphaA
  rw [alphaA_order, h, zero_pow (by norm_num : (65536 : ℕ) ≠ 0)] at hpow
  exact one_ne_zero (hpow.symm)

/-- Assigned rendered compute tree.  Row Inputs
    carry the shared challenge coins `(a,b,c) = (0,0,1)` so
    `ComputeRowsAccepted` matches `cfg` and `WF.rlc5` is inhabited. -/
def computeTree (z α : K) : NTree (ComputeTable.State × ComputeTable.DTcomp K) :=
  mapNTree (fun g => setRowCoins (0 : K) 0 1 g.row)
    (renderRows z α (bfsAssign (mmTreeAir (K := K))))

/-- Assigned annotated memory forest. -/
def memoryForest (z α : K) : List (NTree (MemoryTable.MState × MemoryTable.DTmem K)) :=
  (genMemForestFromTree (encC z) z α MemoryTable.formRDefault (bfsAssign (mmTreeAir (K := K)))).map
    (mapNTree GenMemoryRow.row)

theorem computeTree_size (z α : K) : (computeTree z α).size = 401 := by
  unfold computeTree
  rw [mapNTree_size, renderRows_size, bfsAssign_size]
  unfold mmTreeAir
  rw [airReorder_size, mmTree_size]

theorem computeTree_bfs (z α : K) :
    (bfsForest [computeTree z α]).length = 401 := by
  have := computeTree_size z α
  simpa [bfsForest_length, totalSize] using this

theorem memoryForest_nonempty (z α : K) : memoryForest z α ≠ [] := by
  intro h
  simp [memoryForest, List.map_eq_nil_iff] at h
  exact mmMemForest_nonempty z α h

theorem assigned_kMem (z α : K) :
    (genMemForestFromTree (encC z) z α MemoryTable.formRDefault (bfsAssign (mmTreeAir (K := K)))).length = 618 :=
  mmMemForest_assigned_length (encC z) z α

theorem assigned_memRows (z α : K) :
    totalSize (genMemForestFromTree (encC z) z α MemoryTable.formRDefault (bfsAssign (mmTreeAir (K := K)))) =
      30936 :=
  mmMemForest_assigned_totalSize (encC z) z α

/-- Shared configuration.  Row counts are the measured assigned-generator
    sizes (`401` compute, `618` memory roots, `30936` memory rows).
    `Ksz = 2048` hosts the opcode-active IO list (`accAt ≤ 1203`). -/
noncomputable def cfg (z α : K) : ExactConfig F K where
  challenges :=
    { a := 0, b := 0, c := 1, α := α, z := z, β := 0, γ := 0, lam := MemoryTable.formRDefault }
  Ksz := 2048
  kMem := 618
  orbit := executionOrbit
  orbit_h_pos := by norm_num [executionOrbit]
  compRows := 401
  memRows := 30936
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

/-- Authoritative forest-first execution.  Compute rows are the BFS-assigned
    render; memory rows are the annotated forest of that same assigned tree. -/
noncomputable def exec (z α : K) : ExactExecution (cfg z α) where
  computeTree := computeTree z α
  memoryForest := memoryForest z α
  memoryForest_nonempty := memoryForest_nonempty z α
  memory_root_count := by
    unfold memoryForest
    rw [List.length_map, assigned_kMem]
    simp [cfg]
  compute_bfs_length := by
    change (bfsForest [computeTree z α]).length = 401
    have := computeTree_size z α
    simpa [bfsForest_length, totalSize] using this
  memory_bfs_length := by
    unfold memoryForest
    rw [bfsForest_length, totalSize_map, assigned_memRows]
    simp [cfg]

end

theorem exec_row_counts :
    (exec seedZ alphaA).computeRows.length = 401 ∧
      (exec seedZ alphaA).memoryRows.length = 30936 :=
  ⟨(exec seedZ alphaA).computeRows_length, (exec seedZ alphaA).memoryRows_length⟩

#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.omega_order
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.alphaA_order
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.finrank_cubic
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.cfg
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.computeTree_size
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.computeTree_bfs
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.memoryForest_nonempty
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.assigned_kMem
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.assigned_memRows
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.exec
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.exec_row_counts

end Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537
