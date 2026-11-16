import Nock.NockVMROM.Thm54.Language

/-!
Theorem 5.4 fixes the compute chip `RAP_NockComp-IO` as verifying `N` opcodes
with

* `N` **total number of rows**.

This module proves that statement over the *actual* execution row carrier, not over a
placeholder: `ExactExecution.computeRows` is the BFS projection of the authoritative compute
tree (`Nock/NockVMROM/Thm54/Execution.lean`), and its length is the configured `N =
cfg.compRows`.

To make "`N` is the *opcode* row count" more than a renaming, the module also proves the exact
fibrewise decomposition of the row list over the eleven compute states `OP_0 … OP_9, cons`: every row carries exactly one opcode, so summing the
per-opcode row counts returns `N` on the nose.

The generic fibre-counting lemma in the first section is shared with the memory-side layout
(`Nock/NockVMROM/Thm54/MemoryMplus2L.lean`).
-/

namespace Nock.NockVMROM.Thm54.RowLayout

open Nock Nock.Walk

/-! ## Generic fibre counting over a covering enumeration -/

section Fibre

variable {α β : Type*} [DecidableEq β]

/-- Rows of `l` whose `f`-value is `b`. -/
def fibreCount (f : α → β) (l : List α) (b : β) : ℕ :=
  l.countP (fun a => decide (f a = b))

@[simp] theorem fibreCount_nil (f : α → β) (b : β) : fibreCount f [] b = 0 := rfl

theorem fibreCount_cons (f : α → β) (a : α) (t : List α) (b : β) :
    fibreCount f (a :: t) b = fibreCount f t b + (if f a = b then 1 else 0) := by
  unfold fibreCount
  rw [List.countP_cons]
  by_cases h : f a = b <;> simp [h]

/-- Adding a hit outside the enumeration leaves the fibre total untouched. -/
private theorem sum_add_ite_of_not_mem (g : β → ℕ) (x : β) :
    ∀ E : List β, x ∉ E →
      (E.map (fun b => g b + if x = b then 1 else 0)).sum = (E.map g).sum := by
  intro E
  induction E with
  | nil => intro _; simp
  | cons c rest ih =>
    intro hx
    have hxc : x ≠ c := by
      intro h; exact hx (by simp [h])
    have hxr : x ∉ rest := fun h => hx (List.mem_cons_of_mem _ h)
    simp [hxc, ih hxr]

/-- Adding a hit inside a duplicate-free enumeration raises the fibre total by exactly one. -/
private theorem sum_add_ite_of_mem (g : β → ℕ) (x : β) :
    ∀ E : List β, E.Nodup → x ∈ E →
      (E.map (fun b => g b + if x = b then 1 else 0)).sum = (E.map g).sum + 1 := by
  intro E
  induction E with
  | nil => intro _ hx; exact absurd hx (by simp)
  | cons c rest ih =>
    intro hnd hx
    have hnd' := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hx with hxc | hxr
    · subst hxc
      have hxr : x ∉ rest := hnd'.1
      rw [List.map_cons, List.sum_cons, sum_add_ite_of_not_mem g x rest hxr,
        List.map_cons, List.sum_cons]
      simp
      omega
    · have hxc : x ≠ c := by
        intro h; subst h; exact hnd'.1 hxr
      rw [List.map_cons, List.sum_cons, ih hnd'.2 hxr, List.map_cons, List.sum_cons]
      simp [hxc]
      omega

/-- **Fibre partition of a row list.**  If every row's tag lies in the duplicate-free
enumeration `E`, the per-tag row counts sum to the total row count. -/
theorem sum_fibreCount_eq_length (E : List β) (hE : E.Nodup) (f : α → β) :
    ∀ l : List α, (∀ a ∈ l, f a ∈ E) → (E.map (fibreCount f l)).sum = l.length := by
  intro l
  induction l with
  | nil =>
    intro _
    have hconst : E.map (fibreCount f ([] : List α)) = E.map (fun _ => 0) :=
      List.map_congr_left (fun b _ => by simp [fibreCount])
    rw [hconst]
    simp
  | cons a t ih =>
    intro hcov
    have hfa : f a ∈ E := hcov a (by simp)
    have hcovt : ∀ x ∈ t, f x ∈ E := fun x hx => hcov x (by simp [hx])
    have hmap :
        (E.map (fibreCount f (a :: t))).sum
          = (E.map (fun b => fibreCount f t b + if f a = b then 1 else 0)).sum :=
      congrArg List.sum (List.map_congr_left (fun b _ => fibreCount_cons f a t b))
    rw [hmap, sum_add_ite_of_mem _ (f a) E hE hfa, ih hcovt]
    simp

end Fibre

/-! ## The compute chip's `N` rows -/

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The eleven compute states `OP_0 … OP_9, cons`. -/
def computeStates : List ComputeTable.State :=
  [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .cons]

theorem computeStates_nodup : computeStates.Nodup := by decide

theorem mem_computeStates (s : ComputeTable.State) : s ∈ computeStates := by
  cases s <;> decide

/-- The compute-table row count of one opcode, over the authoritative BFS row list. -/
def opcodeRowCount {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (s : ComputeTable.State) : ℕ :=
  fibreCount (fun row : ComputeTable.State × ComputeTable.DTcomp K => row.1) exec.computeRows s

/-- **`N` total number of rows.**  The derived compute row list — the BFS
projection of the authoritative compute tree — has exactly the configured `N = cfg.compRows`
rows. -/
theorem computeRows_count {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.computeRows.length = cfg.compRows :=
  exec.computeRows_length

/-- The same count, stated directly against the BFS carrier: `N` is the number of nodes of the
authoritative compute tree, with no independent flat row store. -/
theorem computeRows_count_bfs {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    (bfsForest [exec.computeTree]).length = cfg.compRows :=
  exec.compute_bfs_length

/-- **`N` really is the opcode-row count.**  Every compute row carries exactly one of the eleven
opcodes, so the per-opcode row counts sum to `N`. -/
theorem computeRows_opcode_partition {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    (computeStates.map (opcodeRowCount exec)).sum = cfg.compRows := by
  have h :=
    sum_fibreCount_eq_length computeStates computeStates_nodup
      (fun row : ComputeTable.State × ComputeTable.DTcomp K => row.1)
      exec.computeRows (fun row _ => mem_computeStates row.1)
  rw [show (computeStates.map (opcodeRowCount exec)) =
      computeStates.map
        (fibreCount (fun row : ComputeTable.State × ComputeTable.DTcomp K => row.1)
          exec.computeRows) from rfl, h]
  exact exec.computeRows_length

/-- Each opcode row count is bounded by `N`. -/
theorem opcodeRowCount_le {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (s : ComputeTable.State) : opcodeRowCount exec s ≤ cfg.compRows := by
  have hle := List.countP_le_length
    (l := exec.computeRows)
    (p := fun row : ComputeTable.State × ComputeTable.DTcomp K => decide (row.1 = s))
  simpa [opcodeRowCount, fibreCount, exec.computeRows_length] using hle

end

end Nock.NockVMROM.Thm54.RowLayout

#print axioms Nock.NockVMROM.Thm54.RowLayout.sum_fibreCount_eq_length
#print axioms Nock.NockVMROM.Thm54.RowLayout.computeStates_nodup
#print axioms Nock.NockVMROM.Thm54.RowLayout.mem_computeStates
#print axioms Nock.NockVMROM.Thm54.RowLayout.computeRows_count
#print axioms Nock.NockVMROM.Thm54.RowLayout.computeRows_count_bfs
#print axioms Nock.NockVMROM.Thm54.RowLayout.computeRows_opcode_partition
#print axioms Nock.NockVMROM.Thm54.RowLayout.opcodeRowCount_le
