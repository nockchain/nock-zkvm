/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierABuildableParts.lean

  Non-semantic `BuildableNockExecution` side-obligations for the generated
  Tier A OP6/OP2/OP9 program hosted on `DotConfig257` (`F = ZMod 257`,
  `K = GaloisField 257 3`).  Orbit `2^8 = 256` covers 8 compute rows and
  184 memory rows.  Atom bound `q = 257 = ringChar K`.

  `semanticData` / `memoryTrace` / `requestNodup` / `recordCountBalance`
  are not claimed here: those need the per-row language and the served
  forest walk (`Op6LanguageK3` / `Op6BuildablePartsK3` pattern).
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierAConfig
import Nock.NockVMROM.Thm54.Language
import Nock.NockVMROM.Thm54.MemoryMplus2L
import Nock.NockVMROM.Thm54.GenericHonestCommitment

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig257

open Nock Nock.Walk Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

/-! ## Characteristic of the table field -/

instance : CharP K 257 := inferInstance

theorem ringChar_K : ringChar K = 257 :=
  CharP.eq K (ringChar.charP K) (inferInstanceAs (CharP K 257))

/-! ## Opcode-active request / response lengths -/

theorem activeRequestRecords_length_le (pub : ComputeTable.Pub K) :
    (activeRequestRecords pub).length ≤ 3 := by
  unfold activeRequestRecords
  split <;> simp

theorem responseRecords_length_le (pub : MemoryTable.Pub K) :
    (responseRecords pub).length ≤ 1 := by
  unfold responseRecords
  split <;> simp

theorem length_flatMap_le {α β} (l : List α) (f : α → List β) (n : ℕ)
    (h : ∀ x ∈ l, (f x).length ≤ n) :
    (l.flatMap f).length ≤ n * l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    have hx : (f x).length ≤ n := h x (List.mem_cons.mpr (Or.inl rfl))
    have hxs : ∀ y ∈ xs, (f y).length ≤ n := fun y hy =>
      h y (List.mem_cons.mpr (Or.inr hy))
    have := ih hxs
    omega

/-! ## The twelve non-semantic fields that do not need the row web -/

theorem q_gt_one : 1 < (257 : ℕ) := by norm_num

theorem q_le_ringChar : (257 : ℕ) ≤ ringChar K := by
  rw [ringChar_K]

theorem two_ne_zero : (2 : K) ≠ 0 := by
  intro h
  have : 257 ∣ 2 := (CharP.cast_eq_zero_iff K 257 2).mp h
  omega

theorem Ksz_lt_ringChar (z α : K) : (cfg z α).Ksz < ringChar K := by
  rw [ringChar_K]
  norm_num [cfg]

theorem derivedRequestIO_length_le (z α : K) :
    (exec z α).derivedRequestIO.length ≤ 24 := by
  rw [ExactExecution.derivedRequestIO, List.length_map,
    ExactExecution.rawRequests_eq_computeRows]
  have hrows : (exec z α).computeRows.length = 8 :=
    (exec z α).computeRows_length
  have hle := length_flatMap_le (exec z α).computeRows
    (fun row => activeRequestRecords row.2.2.1) 3
    (fun _ _ => activeRequestRecords_length_le _)
  omega

theorem derivedResponseIO_length_le (z α : K) :
    (exec z α).derivedResponseIO.length ≤ 184 := by
  rw [ExactExecution.derivedResponseIO]
  have hrows : (exec z α).memoryRows.length = 184 :=
    (exec z α).memoryRows_length
  have hle := length_flatMap_le (exec z α).memoryRows
    (fun row => if row.2.2.ver = true then [encRecC row.2.2.mem row.2.2.cprime] else []) 1
    (fun _ _ => by split_ifs <;> simp)
  omega

theorem programIOCapacity (z α : K) :
    (exec z α).derivedRequestIO.length + 1 ≤ 2 ^ (cfg z α).orbit.h := by
  have hlen := derivedRequestIO_length_le z α
  have hpow : 2 ^ (cfg z α).orbit.h = 256 := by
    simp [cfg, executionOrbit]
  omega

theorem memoryIOCapacity (z α : K) :
    (exec z α).derivedResponseIO.length + 1 ≤ 2 ^ (cfg z α).orbit.h := by
  have hlen := derivedResponseIO_length_le z α
  have hpow : 2 ^ (cfg z α).orbit.h = 256 := by
    simp [cfg, executionOrbit]
  omega

end Nock.NockVMROM.Thm54.TraceGen.DotConfig257

#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig257.ringChar_K
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig257.two_ne_zero
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig257.programIOCapacity
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig257.memoryIOCapacity
