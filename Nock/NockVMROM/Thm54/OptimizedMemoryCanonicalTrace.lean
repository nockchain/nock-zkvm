import Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization
import Nock.NockVMROM.Thm54.CoordinateCompiler

/-!
# Canonical polynomial trace for optimized memory

The trace has width `180 = 6 + 56·3 + 6`.  Columns `4` and `5` are fixed
first/last-row preprocessing masks, so terminal constraints do not read a fabricated cyclic
successor.  Codec interpolation covers the `174` source cells; residual columns `174..176`
are the dequeue-mask mirror (K-role `56`), and `177..179` host form R `C'`
(K-role `57`), the row's `Pub.cprime`.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedMemoryCanonicalTrace

open Nock
open Nock.Framework
open Module
open scoped Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis
open OptimizedMemoryCoreInventory
open OptimizedMemoryCodec
open OptimizedMemorySemanticRealization

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

def sourceCell (A : SampledIOSameExecutionAssignment R p)
    (b : Basis (Fin 3) F K) (i : Fin R.problem.cfg.memRows) :
    Fin 174 → F
  | j =>
      if hbase : (j : ℕ) < 6 then
        (encodedRowAt (F := F) A i).base ⟨j, hbase⟩
      else
        let role : Fin 56 := ⟨((j : ℕ) - 6) / 3, by omega⟩
        let k : Fin 3 := ⟨((j : ℕ) - 6) % 3, Nat.mod_lt _ (by omega)⟩
        coord b
          ((encodedRowAt (F := F) A i).extension
            (extensionEquiv.symm role)) k

def interpolateColumn {n w : ℕ} (nodes : Fin n → F)
    (cells : Fin n → Fin w → F) (j : Fin w) : F[X] :=
  Lagrange.interpolate Finset.univ nodes (fun i => cells i j)

theorem interpolateColumn_eval {n w : ℕ} (nodes : Fin n → F)
    (hnodes : Function.Injective nodes) (cells : Fin n → Fin w → F)
    (i : Fin n) (j : Fin w) :
    (interpolateColumn nodes cells j).eval (nodes i) = cells i j :=
  Lagrange.eval_interpolate_at_node _ hnodes.injOn (Finset.mem_univ i)

def firstRowMask {n : ℕ} (nodes : Fin n → F) : F[X] :=
  Lagrange.interpolate Finset.univ nodes
    (fun i => if (i : ℕ) = 0 then 1 else 0)

def lastRowMask {n : ℕ} (nodes : Fin n → F) : F[X] :=
  Lagrange.interpolate Finset.univ nodes
    (fun i => if (i : ℕ) + 1 = n then 1 else 0)

/-- Forest root mask: one on walk rows `1..kMem`
(0-indexed `0..kMem-1`), zero after.  The `k = 1` instance is `firstRowMask`. -/
def rootRowMask {n : ℕ} (nodes : Fin n → F) (kMem : ℕ) : F[X] :=
  Lagrange.interpolate Finset.univ nodes
    (fun i => if (i : ℕ) < kMem then 1 else 0)

theorem firstRowMask_eval {n : ℕ} (nodes : Fin n → F)
    (hnodes : Function.Injective nodes) (i : Fin n) :
    (firstRowMask nodes).eval (nodes i) =
      (if (i : ℕ) = 0 then 1 else 0) :=
  Lagrange.eval_interpolate_at_node _ hnodes.injOn (Finset.mem_univ i)

theorem lastRowMask_eval {n : ℕ} (nodes : Fin n → F)
    (hnodes : Function.Injective nodes) (i : Fin n) :
    (lastRowMask nodes).eval (nodes i) =
      (if (i : ℕ) + 1 = n then 1 else 0) :=
  Lagrange.eval_interpolate_at_node _ hnodes.injOn (Finset.mem_univ i)

theorem rootRowMask_eval {n : ℕ} (nodes : Fin n → F) (kMem : ℕ)
    (hnodes : Function.Injective nodes) (i : Fin n) :
    (rootRowMask nodes kMem).eval (nodes i) =
      (if (i : ℕ) < kMem then 1 else 0) :=
  Lagrange.eval_interpolate_at_node _ hnodes.injOn (Finset.mem_univ i)

/-- Dequeue mask: `notLast · (1 − rootMask(next))`.  One on every non-last
row whose successor is not a forest root. -/
def dequeueRowMask {n : ℕ} (nodes : Fin n → F) (kMem : ℕ) : F[X] :=
  Lagrange.interpolate Finset.univ nodes
    (fun i =>
      if (i : ℕ) + 1 = n then 0
      else if (i : ℕ) + 1 < kMem then 0
      else 1)

theorem dequeueRowMask_eval {n : ℕ} (nodes : Fin n → F) (kMem : ℕ)
    (hnodes : Function.Injective nodes) (i : Fin n) :
    (dequeueRowMask nodes kMem).eval (nodes i) =
      (if (i : ℕ) + 1 = n then 0
       else if (i : ℕ) + 1 < kMem then 0
       else 1) :=
  Lagrange.eval_interpolate_at_node _ hnodes.injOn (Finset.mem_univ i)

omit [Fintype K] [DecidableEq K] in
/-- On a `halt` row whose `𝕂` leaf is the
image of a base-field value, that value (`enc_atom`: an honest atom `k` has leaf `(k : K)`); `0`
otherwise.  Seed-free: it reads only the row's own committed leaf. -/
def honestAtomOf (pub : MemoryTable.Pub K) : F :=
  letI := Classical.propDecidable
  if h : pub.st = .halt ∧ ∃ a : F, algebraMap F K a = pub.pt.noun.leaf then h.2.choose else 0

omit [Fintype K] [DecidableEq K] in
theorem honestAtomOf_spec (pub : MemoryTable.Pub K)
    (h : pub.st = .halt ∧ ∃ a : F, algebraMap F K a = pub.pt.noun.leaf) :
    algebraMap F K (honestAtomOf (F := F) pub) = pub.pt.noun.leaf := by
  unfold honestAtomOf
  rw [dif_pos h]
  exact h.2.choose_spec

/-- Canonical polynomial source trace.  Fixed masks replace their equal interpolated codec
columns definitionally, enabling `SatisfiesWithPreprocessing`. -/
def canonicalSourceTrace (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (b : Basis (Fin 3) F K) (kMem : ℕ) : Fin 182 → F[X] :=
  fun j =>
    if hj : (j : ℕ) < 174 then
      let j' : Fin 174 := ⟨j, hj⟩
      if (j : ℕ) = 4 then firstRowMask nodes
      else if (j : ℕ) = 5 then lastRowMask nodes
      else if (j : ℕ) = 153 then rootRowMask nodes kMem
      else if (j : ℕ) = 154 then dequeueRowMask nodes kMem
      else interpolateColumn nodes (sourceCell A b) j'
    else if hk : (j : ℕ) < 177 then
      let k : Fin 3 := ⟨(j : ℕ) - 174, by
        have : 174 ≤ (j : ℕ) := Nat.le_of_not_lt hj
        omega⟩
      Polynomial.C (coord b (1 : K) k) * dequeueRowMask nodes kMem
    else if hc : (j : ℕ) < 180 then
      let k : Fin 3 := ⟨(j : ℕ) - 177, by
        have : 177 ≤ (j : ℕ) := Nat.le_of_not_lt hk
        omega⟩
      Lagrange.interpolate Finset.univ nodes
        (fun i => coord b (R.problem.exec.memoryPubAt i).cprime k)
    else if (j : ℕ) = 180 then
      Lagrange.interpolate Finset.univ nodes
        (fun i => honestAtomOf (F := F) (R.problem.exec.memoryPubAt i))
    else
      Lagrange.interpolate Finset.univ nodes (fun i => honestReqIdx R i)

/-- Physical column `153` is coord `0` of extension role `49`.  Any other role
misses the root-mask column, so the codec interpolation is intact. -/
theorem extRole_ne_rootMask {role : Fin 56} (hrole : (role : ℕ) ≠ 49) (k : Fin 3) :
    6 + 3 * (role : ℕ) + (k : ℕ) ≠ 153 := by
  have hr : (role : ℕ) < 56 := role.isLt
  have hk : (k : ℕ) < 3 := k.isLt
  omega

/-- Physical column `154` is coord `1` of the same dead role `49`. -/
theorem extRole_ne_dequeueMask {role : Fin 56} (hrole : (role : ℕ) ≠ 49) (k : Fin 3) :
    6 + 3 * (role : ℕ) + (k : ℕ) ≠ 154 := by
  have hr : (role : ℕ) < 56 := role.isLt
  have hk : (k : ℕ) < 3 := k.isLt
  omega

theorem canonicalSourceTrace_eval
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (kMem : ℕ)
    (i : Fin R.problem.cfg.memRows) (j : Fin 174)
    (hroot : (j : ℕ) ≠ 153) (hdeq : (j : ℕ) ≠ 154) :
    (canonicalSourceTrace A nodes b kMem ⟨(j : ℕ), Nat.lt_trans j.isLt (by decide)⟩).eval (nodes i) =
      sourceCell A b i j := by
  by_cases h4 : (j : ℕ) = 4
  · have hj : j = ⟨4, by omega⟩ := Fin.ext h4
    rw [hj]
    rw [canonicalSourceTrace, dif_pos (by omega : (4 : ℕ) < 174), if_pos rfl,
      firstRowMask_eval nodes hnodes]
    simp [sourceCell, encodedRowAt, encode, encodeBase,
      semanticRowAt, firstMask]
  by_cases h5 : (j : ℕ) = 5
  · have hj : j = ⟨5, by omega⟩ := Fin.ext h5
    rw [hj]
    rw [canonicalSourceTrace, dif_pos (by decide : (5 : ℕ) < 174),
      if_neg (by decide : (5 : ℕ) ≠ 4), if_pos rfl, lastRowMask_eval nodes hnodes]
    simp [sourceCell, encodedRowAt, encode, encodeBase,
      semanticRowAt, lastMask]
  · rw [canonicalSourceTrace, dif_pos j.isLt, if_neg h4, if_neg h5, if_neg hroot,
      if_neg hdeq, interpolateColumn_eval nodes hnodes]

theorem canonicalSourceTrace_root_fixed
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (b : Basis (Fin 3) F K) (kMem : ℕ) :
    canonicalSourceTrace A nodes b kMem ⟨153, by omega⟩ = rootRowMask nodes kMem := by
  simp [canonicalSourceTrace]

theorem canonicalSourceTrace_dequeue_fixed
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (b : Basis (Fin 3) F K) (kMem : ℕ) :
    canonicalSourceTrace A nodes b kMem ⟨154, by omega⟩ = dequeueRowMask nodes kMem := by
  simp [canonicalSourceTrace]

theorem canonicalSourceTrace_dequeue_mirror
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (b : Basis (Fin 3) F K) (kMem : ℕ) (k : Fin 3) :
    canonicalSourceTrace A nodes b kMem ⟨174 + (k : ℕ), by omega⟩ =
      Polynomial.C (coord b (1 : K) k) * dequeueRowMask nodes kMem := by
  unfold canonicalSourceTrace
  have hj : ¬ ((174 + (k : ℕ) : ℕ) < 174) := Nat.not_lt.mpr (Nat.le_add_right _ _)
  have hk : (174 + (k : ℕ) : ℕ) < 177 := by
    have : (k : ℕ) < 3 := k.isLt
    omega
  rw [dif_neg hj, dif_pos hk]
  refine congrArg (fun t : Fin 3 =>
      Polynomial.C (coord b (1 : K) t) * dequeueRowMask nodes kMem) ?_
  apply Fin.ext
  simp [Nat.add_sub_cancel_left]

/-- Form R `C'` at K-role `57` (physical `177..179`) is the row's `Pub.cprime`. -/
theorem canonicalSourceTrace_cprime
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (kMem : ℕ)
    (i : Fin R.problem.cfg.memRows) (k : Fin 3) :
    (canonicalSourceTrace A nodes b kMem ⟨177 + (k : ℕ), by omega⟩).eval (nodes i) =
      coord b (R.problem.exec.memoryPubAt i).cprime k := by
  unfold canonicalSourceTrace
  have hj : ¬ ((177 + (k : ℕ) : ℕ) < 174) := by
    have : (k : ℕ) < 3 := k.isLt
    omega
  have hk : ¬ ((177 + (k : ℕ) : ℕ) < 177) := Nat.not_lt.mpr (Nat.le_add_right _ _)
  have hc : (177 + (k : ℕ) : ℕ) < 180 := by
    have : (k : ℕ) < 3 := k.isLt
    omega
  rw [dif_neg hj, dif_neg hk, dif_pos hc]
  have hidx :
      (⟨(177 + (k : ℕ) : ℕ) - 177, by
        have : (k : ℕ) < 3 := k.isLt
        omega⟩ : Fin 3) = k := by
    apply Fin.ext
    simp [Nat.add_sub_cancel_left]
  simp only [hidx]
  exact Lagrange.eval_interpolate_at_node _ hnodes.injOn (Finset.mem_univ i)

theorem canonicalSourceTrace_atom
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (kMem : ℕ)
    (i : Fin R.problem.cfg.memRows) :
    (canonicalSourceTrace A nodes b kMem ⟨180, by omega⟩).eval (nodes i) =
      honestAtomOf (F := F) (R.problem.exec.memoryPubAt i) := by
  unfold canonicalSourceTrace
  rw [dif_neg (by decide : ¬ ((180 : ℕ) < 174)), dif_neg (by decide : ¬ ((180 : ℕ) < 177)),
    dif_neg (by decide : ¬ ((180 : ℕ) < 180)), if_pos rfl]
  exact Lagrange.eval_interpolate_at_node _ hnodes.injOn (Finset.mem_univ i)

theorem canonicalSourceTrace_reqIdx
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (kMem : ℕ)
    (i : Fin R.problem.cfg.memRows) :
    (canonicalSourceTrace A nodes b kMem ⟨181, by omega⟩).eval (nodes i) =
      honestReqIdx R i := by
  unfold canonicalSourceTrace
  rw [dif_neg (by decide : ¬ ((181 : ℕ) < 174)), dif_neg (by decide : ¬ ((181 : ℕ) < 177)),
    dif_neg (by decide : ¬ ((181 : ℕ) < 180)), if_neg (by decide)]
  exact Lagrange.eval_interpolate_at_node _ hnodes.injOn (Finset.mem_univ i)

theorem canonicalSourceTrace_first_fixed
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (b : Basis (Fin 3) F K) (kMem : ℕ) :
    canonicalSourceTrace A nodes b kMem ⟨4, by omega⟩ = firstRowMask nodes := by
  simp [canonicalSourceTrace]

theorem canonicalSourceTrace_last_fixed
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (b : Basis (Fin 3) F K) (kMem : ℕ) :
    canonicalSourceTrace A nodes b kMem ⟨5, by omega⟩ = lastRowMask nodes := by
  simp [canonicalSourceTrace]

theorem canonicalSourceTrace_width :
    Fintype.card (Fin 182) = RAPPadding.memoryCoreWidth 3 + 2 := by
  norm_num [RAPPadding.memoryCoreWidth]

end
end OptimizedMemoryCanonicalTrace
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace.canonicalSourceTrace_eval
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace.canonicalSourceTrace_atom
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace.canonicalSourceTrace_first_fixed
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace.canonicalSourceTrace_width
