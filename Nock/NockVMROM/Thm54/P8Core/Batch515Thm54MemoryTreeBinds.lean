/-
  Nock/NockVMROM/Thm54/P8Core/Batch515Thm54MemoryTreeBinds.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch515Thm54MemoryTreeBinds`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch515Thm54MemoryTreeBinds.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackageDefs
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch515

open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.SemanticStrategy
variable {K : Type} [Field K]

/-- Structure is hereditary. -/
theorem MemoryFingerprintStructure.of_InTree {z : K}
    {root node : NTree (MState × DTmem K)}
    (h : MemoryFingerprintStructure z root)
    (hin : InTree root node) :
    MemoryFingerprintStructure z node := by
  induction h generalizing node with
  | halt data atomShape =>
    cases hin with
    | here => exact MemoryFingerprintStructure.halt data atomShape
    | sub hs _ => simp [NTree.children_node] at hs
  | decompose data left right consEq hL hR ihL ihR =>
    cases hin with
    | here =>
      exact MemoryFingerprintStructure.decompose data left right consEq hL hR
    | sub hs hrest =>
      simp [NTree.children_node, List.mem_cons] at hs
      rcases hs with rfl | rfl
      · exact ihL hrest
      · exact ihR hrest
  | readRoot data child passEq childStructure ih =>
    cases hin with
    | here =>
      exact MemoryFingerprintStructure.readRoot data child passEq childStructure
    | sub hs hrest =>
      simp [NTree.children_node] at hs
      subst hs
      exact ih hrest
  | verifyChild data child passEq childStructure ih =>
    cases hin with
    | here =>
      exact MemoryFingerprintStructure.verifyChild data child passEq childStructure
    | sub hs hrest =>
      simp [NTree.children_node] at hs
      subst hs
      exact ih hrest

theorem MemoryFingerprintStructure.of_bfsForest {z : K}
    {forest : List (NTree (MState × DTmem K))}
    {t : NTree (MState × DTmem K)}
    (h : ∀ root ∈ forest, MemoryFingerprintStructure z root)
    (ht : t ∈ bfsForest forest) :
    MemoryFingerprintStructure z t := by
  obtain ⟨root, hroot, hin⟩ := (mem_bfsForest forest t).1 ht
  exact MemoryFingerprintStructure.of_InTree (h root hroot) hin

end Nock.RedTeam.Batch515
