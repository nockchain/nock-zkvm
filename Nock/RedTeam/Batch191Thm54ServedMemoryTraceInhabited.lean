/-
  Nock/RedTeam/Batch191Thm54ServedMemoryTraceInhabited.lean

  **`ExactServedMemoryTrace` inhabited at the generated carrier.**

  `ES.2` is
  this repo's record of three counted conditions that turned out to exclude nothing.

  `b191Mt` is a **term** of
  `ExactServedMemoryTrace 769 DotConfig769.Λ b216Cfg b216Exec b216Data`, so the whole premise list
  is jointly satisfiable at a real program.

  The only new proof required was `b191_hKsz2 : 2 * kMem ≤ 64`, three lines off `Batch196.b196_kMem`.
  It cannot conflict with `hKsz`: `ExactConfig.Ksz` is a bare `ℕ` with no upper constraint
  (`Config.lean:96`), so `Ksz := max (2 * kMem) accAt` is available for any program.  Every other
  hypothesis is a pre-existing `Batch180` / `Batch216` discharge.

  **Non-vacuity is checked on the assembled object, not on the batches it was built from**:
  `b191Mt.roots = Batch196.b196Roots` by `rfl`, the aggregate timestamp list has 13 entries and is
  `Nodup`, and `b191_coverage_witnessed` exhibits row 5's served lookup being served from a built
  root.  `b191_lmio` is the payoff — `intermediateMatching` closes the paper's global `intermediate`
  condition at the generated carrier.

  **Scope.**  One configuration, one program.  Nothing here is a capstone: `genBuildable` still wants `hnodup`, and `Data`,
  `Inputs` and the statement are untouched.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenServedMemoryTrace
import Nock.RedTeam.Batch216Thm54SemanticCoverageAtTierA
import Nock.RedTeam.Batch211Thm54TimestampNodupAtTierA

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Nock.RedTeam.Batch191
open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.Framework.Thm54
open Nock.RedTeam

abbrev DK := DotConfig769.K
abbrev DF := DotConfig769.F
noncomputable local instance : Fintype DK := Fintype.ofFinite _
noncomputable local instance : DecidableEq DK := Classical.decEq _
noncomputable section

theorem b191_hKsz2 :
    2 * (genExactConfig (F := DF) Batch216.b216Chal 64 executionOrbit Batch216.b216_horb
      (genComputeRows seedZ alphaA (dotTree (K := DK)))
      (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))
      Batch216.b216_mempos Batch216.b216_comp_le Batch216.b216_mem_le).kMem ≤ 64 := by
  have h : Batch196.b196Cfg.kMem = 10 := Batch196.b196_kMem
  rw [Batch196.b196Cfg, genExactConfig_kMem] at h
  rw [genExactConfig_kMem, h]
  norm_num

def b191Mt
     :
    ExactServedMemoryTrace 769 DotConfig769.Λ Batch216.b216Cfg Batch216.b216Exec
      Batch216.b216Data Batch216.b216ExecA :=
  genServedMemoryTrace (F := DF) seedZ alphaA seedZ_ne_zero two_ne_zero 0 0 0
    Batch216.b216Chal Batch180.dot_hinp (DotConfig769.memoryInputs_eq _ _)
    64 executionOrbit Batch216.b216_horb (genComputeSkeleton_dot 0)
    (Batch180.dot_seedGood _) (Batch180.dot_computeCoins _ _ _ _ _)
    (by norm_num [DotConfig769.Λ]) Batch180.dot_air_traceConfined
    Batch216.b216_mempos Batch216.b216_comp_le Batch216.b216_mem_le
    192 (le_of_eq Batch180.alphaA_order_eq_192.symm)
    (by have := Batch180.dot_accAt_le; omega)
    (by have := Batch180.dot_accAt_le; omega)
    b191_hKsz2
    Batch180.dot_hb (by norm_num) DotConfig769.ringChar_K.symm Batch180.dot_haxis
    (Batch180.not_mem_badSeeds_of_pairs _ _ Batch180.dot_gen_pairs_sep)
    Batch180.dot_gen_hout Batch180.dot_hlt


-- the assembled object's roots ARE the measured ones
example : b191Mt.roots = Batch196.b196Roots := rfl
example : b191Mt.roots = Batch216.b216Roots := rfl

-- and its aggregate timestamp list is the measured thirteen
theorem b191_len_13 :
    ((List.finRange Batch216.b216Cfg.kMem).flatMap
      (fun i => (b191Mt.roots i).timestampPowers)).length = 13 :=
  Batch211.b211_length_eq_13

-- the four fields, read back off the assembled structure
theorem b191_nodup :
    ((List.finRange Batch216.b216Cfg.kMem).flatMap
      (fun i => (b191Mt.roots i).timestampPowers)).Nodup :=
  b191Mt.timestampPowersNodup

theorem b191_coverage :
    ∀ row : Fin Batch216.b216Cfg.compRows,
      ∀ lookup ∈ (Batch216.b216Data.rows row).needs.served,
        ∃ (i : Fin Batch216.b216Cfg.kMem) (s : Service Batch216.b216Cfg Batch216.b216ExecA),
          s ∈ (b191Mt.roots i).services ∧ s.record = lookup.record ∧ s.root = lookup.root ∧
            s.child = lookup.child ∧ s.axis = lookup.axis := b191Mt.semanticCoverage

-- the derived paper-level consequence: LmIO closes on the aggregate
theorem b191_lmio :
    IO.LmIO Batch216.b216Cfg.Ksz
      (forestReadTimestamps Batch216.b216Cfg Batch216.b216ExecA)
      (forestVerifyTimestamps Batch216.b216Cfg Batch216.b216ExecA) :=
  b191Mt.intermediateMatching

theorem b191_coverage_witnessed (h5 : (5 : ℕ) < Batch216.b216Cfg.compRows) :
    ∃ lookup ∈ (Batch216.b216Data.rows ⟨5, h5⟩).needs.served,
      ∃ (i : Fin Batch216.b216Cfg.kMem) (s : Service Batch216.b216Cfg Batch216.b216ExecA),
        s ∈ (b191Mt.roots i).services ∧ s.record = lookup.record ∧ s.root = lookup.root ∧
          s.child = lookup.child ∧ s.axis = lookup.axis := by
  have hlen := Batch216.b216_served_length_five h5
  obtain ⟨l, hl⟩ : ∃ l, l ∈ (Batch216.b216Data.rows ⟨5, h5⟩).needs.served := by
    refine List.exists_mem_of_ne_nil _ ?_
    intro hnil; rw [hnil] at hlen; simp at hlen
  exact ⟨l, hl, b191Mt.semanticCoverage ⟨5, h5⟩ l hl⟩

end
end Nock.RedTeam.Batch191
#print axioms Nock.RedTeam.Batch191.b191Mt
#print axioms Nock.RedTeam.Batch191.b191_len_13
#print axioms Nock.RedTeam.Batch191.b191_lmio
#print axioms Nock.RedTeam.Batch191.b191_coverage_witnessed
