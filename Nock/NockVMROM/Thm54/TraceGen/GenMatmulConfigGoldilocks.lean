/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulConfigGoldilocks.lean

  `ExactConfig` for the generated 2×2 matmul program, over the paper's Goldilocks
  carrier `F = Field.Fp` and table field `K = GaloisField Field.p 3`.

  `MatmulConfig65537` is kept intact.  This namespace is the same Nock program
  (`mmSubject`, `mmFormula`, result `mmC`) on the field that can inhabit both
  the 30936-row forest and `packageOrbit : StrictOrbitDomain F 3 h`.  The orbits are the existing
  Goldilocks inhabitants (`GoldilocksOrbit.goldilocksStrictOrbit 16`,
  `goldilocksExecutionOrbit 16`); nothing is invented at 65537, and 769 is not
  a target (`401 > 2^8`).

  Assigned forest counts 618 / 30936 and compute 401 are program facts, reused
  from the field-polymorphic `mmTree_size` / `mmMemForest_assigned_*`.
-/
import Nock.Field
import Nock.NockVMROM.Thm54.CoordinateBasis
import Nock.NockVMROM.Thm54.Execution
import Nock.NockVMROM.Thm54.ExtensionField
import Nock.NockVMROM.Thm54.GoldilocksOrbit
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulSize
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulData
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulMemSize
import Nock.NockVMROM.Thm54.TraceGen.GenWF
import Nock.NockVMROM.Thm54.ExactTraversal
import Mathlib.FieldTheory.Finite.GaloisField
import Nock.NockVMROM.Thm54.ForestExponentWindow

namespace Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks

open Nock Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.GoldilocksOrbit

/-- Goldilocks base field. -/
abbrev F : Type := Field.Fp
/-- Degree-3 table field. -/
abbrev K : Type := Field.K

instance : CharP K (ringChar K) := ringChar.charP K

noncomputable abbrev φ : F →+* K := algebraMap F K
theorem φ_injective : Function.Injective φ := RingHom.injective φ

theorem finrank_cubic : Module.finrank F K = 3 :=
  GaloisField.finrank Field.p (by norm_num)

/-- `bas` residual: the cubic has a 3-element `F`-basis. -/
noncomputable def basis : Module.Basis (Fin 3) F K :=
  stdCoordBasis F K 3 finrank_cubic

/-- Execution orbit of order `2^16` in `K`, cubed out of the strict generator
    (`GoldilocksOrbit.goldilocksExecutionOrbit`) -/
noncomputable def executionOrbit : OrbitDomain K :=
  goldilocksExecutionOrbit 16 (by norm_num) (by norm_num)

/-- Strict RAP orbit of order `3 · 2^16` in `F`.
    Reuses `b291_goldilocks_packageOrbit`'s inhabitant. -/
noncomputable def packageOrbit : StrictOrbitDomain F 3 16 :=
  goldilocksStrictOrbit 16 (by norm_num) (by norm_num)

theorem executionOrbit_h : executionOrbit.h = 16 := rfl

theorem executionOrbit_order :
    orderOf executionOrbit.ω = 2 ^ 16 :=
  goldilocksExecutionGenerator_order 16 (by norm_num)

theorem packageOrbit_order :
    orderOf packageOrbit.ω = 3 * 2 ^ 16 :=
  goldilocksStrictGenerator_order 16 (by norm_num)

theorem horb : 1 ≤ executionOrbit.h := by
  norm_num [executionOrbit, goldilocksExecutionOrbit]

theorem hcap : 2 ^ executionOrbit.h ≤ 2 ^ (16 : ℕ) := by
  simp [executionOrbit_h]

noncomputable section

/-- NPR seed of order `2^32` in `K`, the algebra image of `7^(2^32−1)` in `𝔽_p`.
    `φ(8)` has order `64` (`GoldilocksOrbit.eight_order`) and cannot discharge
    `hout` at `Λ = 568`. -/
def seedZ : K := φ goldilocksSeedBase
/-- Honest `α` is the execution-orbit generator (`orderOf = 2^16`). -/
def alphaA : K := executionOrbit.ω

theorem eight_ne_zero : (8 : F) ≠ 0 :=
  eight_ne_zero_fp

theorem seedZ_ne_zero : seedZ ≠ 0 := by
  intro h
  exact goldilocksSeedBase_ne_zero (φ_injective (by simpa [seedZ] using h))

theorem seedZ_order : orderOf seedZ = 2 ^ 32 := by
  have h := orderOf_injective φ.toMonoidHom φ_injective goldilocksSeedBase
  rw [goldilocksSeedBase_order] at h
  simpa [seedZ] using h

theorem seedZ_order_gt (Λ : ℕ) (hΛ : Λ < 2 ^ 32) : Λ < orderOf seedZ := by
  rw [seedZ_order]; exact hΛ

theorem alphaA_order : orderOf alphaA = 2 ^ 16 :=
  executionOrbit_order

theorem alphaA_ne_zero : alphaA ≠ 0 := by
  intro h
  have hpow := pow_orderOf_eq_one alphaA
  rw [alphaA_order, h, zero_pow (by norm_num : (2 ^ 16 : ℕ) ≠ 0)] at hpow
  exact one_ne_zero (hpow.symm)

theorem ringChar_K : ringChar K = Field.p := by
  rw [← Algebra.ringChar_eq F K, ZMod.ringChar_zmod_n]

theorem two_ne_zero : (2 : K) ≠ 0 := by
  have h2 : 2 < Field.p := by
    simp only [Field.p]; norm_num
  exact CharP.cast_eq_zero_iff K (ringChar K) 2 |>.not.mpr (by
    rw [ringChar_K]
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) h2)

theorem hq : 11 < Field.p := by
  simp only [Field.p]; norm_num

theorem hchar : Field.p = ringChar K :=
  ringChar_K.symm

/-- Assigned rendered compute tree. -/
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

    `a := 0, b := 0, c := 1` and `Ksz := 2048` are the forest-first host
    (`computeTree` stamps `setRowCoins 0 0 1`; `2048` hosts `accAt ≤ 1203`).
    `nockCompiles_of_grom_atTree_p62` / `nockCompiles_p67` use
    `compilerChallengeVector` at the *obtained* coins
    (`mm_exists_computeCoins`) and `compilerKszOf = 1236`
    (`GenMatmulGoldilocksResiduals.lean::mm_compilerKsz`).  The coins are
    existential (`Batch297Thm54P5InstantiationReview.lean::b297_hcoins_is_exists`), so this config
    cannot carry the compiled triple.  Receipts: `cfg_legacy_coins`,
    `cfg_legacy_Ksz`, `cfg_challenges_are_compiler_placeholders`,
    `cfg_Ksz_ne_compilerKszOf_numeral` -/
noncomputable def cfg (z α : K) : ExactConfig F K where
  challenges :=
    { a := 0, b := 0, c := 1, α := α, z := z, β := 0, γ := 0, lam := MemoryTable.formRDefault }
  Ksz := 2048
  kMem := 618
  orbit := executionOrbit
  orbit_h_pos := horb
  compRows := 401
  memRows := 30936
  compRows_pos := by norm_num
  memRows_pos := by norm_num
  compRows_le := by
    rw [executionOrbit_h]
    norm_num
  memRows_le := by
    rw [executionOrbit_h]
    norm_num
  eDeg := 1
  eDeg_eq_one := rfl
  compNodes := fun i => executionOrbit.orbitPoint i
  compNodes_spec := by intro i; rfl
  memNodes := fun i => executionOrbit.orbitPoint i
  memNodes_spec := by intro i; rfl

/-- The fixture's configured `λ` is `formRDefault`. -/
@[simp] theorem cfg_lam (z α : K) : (cfg z α).challenges.lam = MemoryTable.formRDefault := rfl

/-- Authoritative forest-first execution. -/
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

/-- ExactConfig coins are the placeholder triple, not the
    obtained p62 coins -/
theorem cfg_legacy_coins (z α : K) :
    (cfg z α).challenges.a = 0 ∧
      (cfg z α).challenges.b = 0 ∧
      (cfg z α).challenges.c = 1 :=
  ⟨rfl, rfl, rfl⟩

theorem cfg_legacy_Ksz (z α : K) :
    (cfg z α).Ksz = 2048 :=
  rfl

/-- The placeholders are exactly `compilerChallengeVector α z 0 0 1`
    (`GenNockCompilesBounded.lean::compilerChallengeVector`).  Compiled
    instances substitute the obtained triple.  Stated fieldwise so this
    config file does not import the compiler module. -/
theorem cfg_challenges_are_compiler_placeholders (z α : K) :
    (cfg z α).challenges.a = 0 ∧
      (cfg z α).challenges.b = 0 ∧
      (cfg z α).challenges.c = 1 ∧
      (cfg z α).challenges.α = α ∧
      (cfg z α).challenges.z = z ∧
      (cfg z α).challenges.β = 0 ∧
      (cfg z α).challenges.γ = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cfg_Ksz_ne_compilerKszOf_numeral :
    (2048 : ℕ) ≠ 1236 := by
  decide

end

theorem exec_row_counts :
    (exec seedZ alphaA).computeRows.length = 401 ∧
      (exec seedZ alphaA).memoryRows.length = 30936 :=
  ⟨(exec seedZ alphaA).computeRows_length, (exec seedZ alphaA).memoryRows_length⟩

/-- Compute 401 and memory 30936 both sit in the Goldilocks `2^16` orbit. -/
theorem hosts_matmul_rows :
    401 ≤ 2 ^ 16 ∧ 30936 ≤ 2 ^ 16 := by
  constructor <;> norm_num

/-- Goldilocks `|K| = p^3` is far larger; the 65537 numeral is already enough. -/
theorem hcard_arith :
    28 * 30936 * 30936 + 4 * 30936 < Field.p ^ 3 := by
  simp only [Field.p]
  norm_num

#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.finrank_cubic
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.packageOrbit_order
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.executionOrbit_order
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.seedZ_ne_zero
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.seedZ_order
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.computeTree_size
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.memoryForest_nonempty
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.assigned_kMem
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.assigned_memRows
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.exec_row_counts
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.hcard_arith
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.cfg_legacy_coins
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.cfg_legacy_Ksz
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.cfg_challenges_are_compiler_placeholders
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.cfg_Ksz_ne_compilerKszOf_numeral

end Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks
