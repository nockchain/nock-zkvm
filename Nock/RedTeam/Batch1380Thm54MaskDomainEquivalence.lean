import Nock.NockVMROM.Thm54.OptimizedMemoryRAP
import Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
/-!
  Nock/RedTeam/Batch1380Thm54MaskDomainEquivalence.lean
-/
/-!
Scope-zerofier probe: mask form ↔ per-kind-domain (zerofier) form, pointwise, for ANY trace
whose mask column is the bound preprocessing polynomial (`BindsPreprocessing`).  The body `G`
is an arbitrary function of the row node, so the statement covers honest and hostile traces.
-/
open Nock Nock.Framework Nock.NockVMROM.Thm54 Polynomial
open Nock.NockVMROM.Thm54.CoordinateCompiler

namespace Nock.RedTeam.Batch1380
variable {F : Type} [Field F]

/-- Zerofier domain of a 0/1 mask on the row nodes: the nodes where it is `1`. -/
noncomputable def maskDomain {n : ℕ} (nodes : Fin n → F) (v : Fin n → F) : Finset F := by
  classical exact (Finset.univ.filter (fun i => v i = 1)).image nodes

/-- **Generic equivalence.** If the bound mask `m` takes the 0/1 values `v` at the row nodes,
then "`m · G` vanishes on every row" iff "`G` vanishes on the zerofier domain of `m`". -/
theorem masked_iff_domain {n : ℕ} (nodes : Fin n → F) (v : Fin n → F)
    (hv : ∀ i, v i = 0 ∨ v i = 1) (m : F[X]) (hm : ∀ i, m.eval (nodes i) = v i) (G : F → F) :
    (∀ x ∈ rowNodeSet nodes, m.eval x * G x = 0) ↔ (∀ x ∈ maskDomain nodes v, G x = 0) := by
  classical
  constructor
  · intro h x hx
    simp only [maskDomain, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have := h (nodes i) (by simp [rowNodeSet])
    rw [hm i, hi, one_mul] at this
    exact this
  · intro h x hx
    simp only [rowNodeSet, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [hm i]
    rcases hv i with h0 | h1
    · rw [h0, zero_mul]
    · rw [h1, one_mul]
      exact h _ (by simp only [maskDomain, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨i, h1, rfl⟩)

/-! ## One instance per kind, at the deployed mask polynomials -/

/-- boundary (`isFirst`, compute col 11 / memory col 4): domain = `{node 0}`. -/
theorem boundary_iff {n : ℕ} (nodes : Fin n → F) (hinj : Function.Injective nodes) (G : F → F) :
    (∀ x ∈ rowNodeSet nodes, (Nock.Framework.firstRowMask nodes).eval x * G x = 0) ↔
      (∀ i : Fin n, (i : ℕ) = 0 → G (nodes i) = 0) := by
  classical
  rw [masked_iff_domain nodes (fun i => if (i : ℕ) = 0 then 1 else 0)
    (fun i => by by_cases h : (i : ℕ) = 0 <;> simp [h]) _
    (Nock.Framework.firstRowMask_eval nodes hinj) G]
  simp [maskDomain]

/-- terminal (`isLast`, compute col 12): domain = `{node (n-1)}`. -/
theorem terminal_iff {n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (hinj : Function.Injective nodes)
    (G : F → F) :
    (∀ x ∈ rowNodeSet nodes, (Nock.Framework.lastRowMask hn nodes).eval x * G x = 0) ↔
      (∀ i : Fin n, i = ⟨n - 1, by omega⟩ → G (nodes i) = 0) := by
  classical
  rw [masked_iff_domain nodes (fun i => if i = ⟨n - 1, by omega⟩ then 1 else 0)
    (fun i => by by_cases h : i = ⟨n - 1, by omega⟩ <;> simp [h]) _
    (Nock.Framework.lastRowMask_eval hn nodes hinj) G]
  simp [maskDomain]

/-- transition (`1 − isLast`): domain = every node but the last. -/
theorem transition_iff {n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (hinj : Function.Injective nodes)
    (G : F → F) :
    (∀ x ∈ rowNodeSet nodes, (1 - Nock.Framework.lastRowMask hn nodes).eval x * G x = 0) ↔
      (∀ i : Fin n, i ≠ ⟨n - 1, by omega⟩ → G (nodes i) = 0) := by
  classical
  rw [masked_iff_domain nodes (fun i => if i = ⟨n - 1, by omega⟩ then 0 else 1)
    (fun i => by by_cases h : i = ⟨n - 1, by omega⟩ <;> simp [h]) _
    (fun i => by
      simp only [eval_sub, eval_one, Nock.Framework.lastRowMask_eval hn nodes hinj]
      split_ifs <;> simp) G]
  simp [maskDomain]

/-- row: no mask, domain = all nodes (identity; stated for completeness). -/
theorem row_iff {n : ℕ} (nodes : Fin n → F) (G : F → F) :
    (∀ x ∈ rowNodeSet nodes, G x = 0) ↔ (∀ i : Fin n, G (nodes i) = 0) := by
  classical
  simp [rowNodeSet]

/-- the memory forest `rootMask` (rows `< kMem`) is a NON-standard domain: no client zerofier. -/
theorem rootMask_iff {n : ℕ} (nodes : Fin n → F) (hinj : Function.Injective nodes) (kMem : ℕ)
    (G : F → F) :
    (∀ x ∈ rowNodeSet nodes,
        (OptimizedMemoryCanonicalTrace.rootRowMask nodes kMem).eval x * G x = 0) ↔
      (∀ i : Fin n, (i : ℕ) < kMem → G (nodes i) = 0) := by
  classical
  rw [masked_iff_domain nodes (fun i => if (i : ℕ) < kMem then 1 else 0)
    (fun i => by by_cases h : (i : ℕ) < kMem <;> simp [h]) _
    (OptimizedMemoryCanonicalTrace.rootRowMask_eval nodes kMem hinj) G]
  simp [maskDomain]

/-! ## Tie to deployed gate bodies: at a bound env the masked gate is literally `mask(x) · body(x)`. -/

/-- compute boundary gate `isFirst · S` (`expInitGate`). -/
theorem expInitGate_eval (env : Nock.Reified.Env F) :
    (OptimizedComputeCorrectedFinal.expInitGate (F := F)).eval env =
      env.trace 11 * env.trace OptimizedComputeCorrectedFinal.computeExpCol := by
  simp [OptimizedComputeCorrectedFinal.expInitGate, CoeffExpr.eval]

/-- compute transition gate `(1 − isLast) · (S' − S − arity)` (`expStepGate`). -/
theorem expStepGate_eval (env : Nock.Reified.Env F) :
    (OptimizedComputeCorrectedFinal.expStepGate (F := F)).eval env =
      (1 - env.trace 12) *
        (env.traceNext OptimizedComputeCorrectedFinal.computeExpCol -
          env.trace OptimizedComputeCorrectedFinal.computeExpCol -
          (OptimizedComputeCorrectedFinal.arityForm (F := F)).eval env) := by
  simp [OptimizedComputeCorrectedFinal.expStepGate, CoeffExpr.eval]

/-- compute terminal equality check `isLast · (trace_{31+i} − pub_{62+i})`. -/
theorem lastEqCheck_eval (env : Nock.Reified.Env F) (i : ℕ) :
    (OptimizedComputeFinal.endpointEqualityCheck (OptimizedComputeBaseGates.isLastVar (F := F)) 31 i).eval env =
      env.trace 12 * (env.trace i - env.pub (31 + i)) := by
  simp [OptimizedComputeFinal.endpointEqualityCheck, OptimizedComputeBaseGates.isLastVar,
    OptimizedComputeBaseGates.bv, CoeffExpr.eval]

end Nock.RedTeam.Batch1380

#print axioms Nock.RedTeam.Batch1380.masked_iff_domain
#print axioms Nock.RedTeam.Batch1380.boundary_iff
#print axioms Nock.RedTeam.Batch1380.terminal_iff
#print axioms Nock.RedTeam.Batch1380.transition_iff
#print axioms Nock.RedTeam.Batch1380.rootMask_iff
#print axioms Nock.RedTeam.Batch1380.expInitGate_eval
#print axioms Nock.RedTeam.Batch1380.expStepGate_eval
#print axioms Nock.RedTeam.Batch1380.lastEqCheck_eval
