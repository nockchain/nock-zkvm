/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHWalkGlue.lean

* `walkRows_root_cells`: from `hwcell` (every walk node is a cell of `cells`) every walk row's ROOT is in `cells`
    (the root of a row's tree is itself a row, at len 0, whose node is its root).  This discharges the `hwroot` binder of the walk-column lemma.
  * `hwcell_reg`, `hwroot_reg`: the same at the regrouped read list `regroup rs`, `cells` unchanged.
  * `walkGenRowsB_size`: the exec table has `ws.length` rows.
  * `dsB_getD`: the `j`-th `walkDB` entry of the exec row data list.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalk
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkOrd

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkGlue

open Nock Nock.Walk Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalk
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkOrd

/-- **Every walk row's root is a cell of `cells`**, given that every walk node is. -/
theorem walkRows_root_cells (cells : List Noun) (rs : List (Noun × ℕ))
    (hwcell : ∀ u ∈ walkRows cells rs, u.label.node ∈ cells) :
    ∀ u ∈ walkRows cells rs, u.label.root ∈ cells ∨ u.label.root.isCell = false := by
  intro u hu
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp hu
  have hcmem : c ∈ walkRows cells rs := (mem_bfsForest _ _).mpr ⟨c, hc, InTree.here c⟩
  have hnode : c.label.node ∈ cells := hwcell c hcmem
  have hroot : c.label.node = c.label.root := by
    rcases mem_walkForest hc with ⟨-, h⟩ | ⟨r, -, h⟩ <;> rw [h] <;>
      exact (trie_label _ _ _ _).1.trans (trie_label _ _ _ _).2.2.symm
  have hur : u.label.root = c.label.root := by
    rcases mem_walkForest hc with ⟨-, h⟩ | ⟨r, -, h⟩
    · obtain ⟨n', bs', T', hu', -⟩ := inTree_trie_inv _ (fun _ _ _ => True) (fun _ _ _ _ _ _ _ => trivial)
        (h ▸ hin) _ _ _ rfl trivial
      rw [hu', h, (trie_label _ _ _ _).2.2, (trie_label _ _ _ _).2.2]
    · obtain ⟨n', bs', T', hu', -⟩ := inTree_trie_inv _ (fun _ _ _ => True) (fun _ _ _ _ _ _ _ => trivial)
        (h ▸ hin) _ _ _ rfl trivial
      rw [hu', h, (trie_label _ _ _ _).2.2, (trie_label _ _ _ _).2.2]
  left
  rw [hur, ← hroot]; exact hnode

/-- `hwcell` at the regrouped reads (the walk rows are a permutation). -/
theorem hwcell_reg (cells : List Noun) (rs : List (Noun × ℕ)) (hall : ∀ x ∈ rs, VclL.isPathAx x.2 = true)
    (hwcell : ∀ u ∈ walkRows cells rs, u.label.node ∈ cells) :
    ∀ u ∈ walkRows cells (regroup rs), u.label.node ∈ cells :=
  fun u hu => hwcell u ((walkRows_regroup_perm cells rs hall).mem_iff.mp hu)

/-- `hwroot` at the regrouped reads, from `hwcell` at the original reads. -/
theorem hwroot_reg (cells : List Noun) (rs : List (Noun × ℕ)) (hall : ∀ x ∈ rs, VclL.isPathAx x.2 = true)
    (hwcell : ∀ u ∈ walkRows cells rs, u.label.node ∈ cells) :
    ∀ u ∈ walkRows cells (regroup rs), u.label.root ∈ cells ∨ u.label.root.isCell = false :=
  walkRows_root_cells cells (regroup rs) (hwcell_reg cells rs hall hwcell)

/-- The exec walk table has one row per `ws` entry. -/
theorem walkGenRowsB_size (k : Co) (y : K6) (α γ : K3) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cert : ℕ → ℕ → ℕ)
    (cs : List Noun) (ws : List WRow) (kr : ℕ) :
    (walkGenRowsB k y α γ H rI cert cs ws kr).1.size = ws.length := by
  unfold walkGenRowsB
  simp

/-- The `j`-th exec row datum is `walkDB` at the `j`-th row. -/
theorem dsB_getD (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun) (ws : List WRow) (j : ℕ)
    (hj : j < ws.length) (z : WalkD) (d : WRow) :
    ((ws.zipIdx 0).map fun (w, j) => walkDB k y H rI cs w j).getD j z = walkDB k y H rI cs (ws.getD j d) j :=
  dsL_getD k y H rI cs ws j hj z d

#print axioms walkRows_root_cells
#print axioms hwcell_reg
#print axioms hwroot_reg
#print axioms walkGenRowsB_size
#print axioms dsB_getD

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkGlue
