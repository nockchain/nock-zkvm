/-
  Nock/NockVMROM/Thm54/P8Core/Batch524Thm54DecodeMemoryRowIn.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch524Thm54DecodeMemoryRowIn`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch524Thm54DecodeMemoryRowIn.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.MemoryTopoBetaFree
import Nock.NockVMROM.Thm54.P8Core.Batch516Thm54ComputeJoinSound

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch524

open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.RedTeam.Batch515
open Nock.RedTeam.Batch516 (ServedFingerprint)
open scoped Classical
variable {K : Type} [Field K] [DecidableEq K]

theorem nounByFP_of_served {q : ℕ}
    {forest : List (NTree (MState × DTmem K))} {fp : FP K}
    (h : ServedFingerprint forest fp) :
    ∃ t ∈ bfsForest forest,
      t.label.2.2.pt.noun = fp ∧ nounByFP q forest fp = decodeNoun q t := by
  unfold nounByFP
  cases hfind : (bfsForest forest).find? (fun t => t.label.2.2.pt.noun = fp) with
  | none =>
    obtain ⟨t, ht, hfp⟩ := h
    have hnone := List.find?_eq_none.mp hfind t ht
    simp at hnone
    exact (hnone hfp).elim
  | some t =>
    refine ⟨t, List.mem_of_find?_eq_some hfind, ?_, rfl⟩
    have hp := List.find?_some hfind
    simpa using hp

theorem bindFP_of_nounByFP_hit {z : K} (hz : z ≠ 0) {q : ℕ}
    {forest : List (NTree (MState × DTmem K))} {fp : FP K}
    (hstruct : ∀ t ∈ bfsForest forest, MemoryFingerprintStructure z t)
    (hleaves : ∀ t ∈ bfsForest forest, MemoryLeafAtomsRealized q t)
    (hhit : ServedFingerprint forest fp) :
    bindFP z (nounByFP q forest fp) fp := by
  obtain ⟨t, ht, hfp, hnoun⟩ := nounByFP_of_served (q := q) hhit
  rw [hnoun, bindFP, ← hfp]
  exact (decode_fingerprint hz (hstruct t ht) (hleaves t ht)).symm

/-- Forest facts `nounByFP` needs for the paper-`⊥` halves. -/
def ForestFPFacts (z : K) (q : ℕ)
    (forest : List (NTree (MState × DTmem K))) : Prop :=
  (∀ u ∈ bfsForest forest, MemoryFingerprintStructure z u) ∧
    (∀ u ∈ bfsForest forest, MemoryLeafAtomsRealized q u)

theorem bindFP_halt_parent {z : K} {q : ℕ} {data : DTmem K}
    (hatom : data.2.pt.noun.size = z ∧ data.2.pt.noun.dyck = 0)
    (hleaves : MemoryLeafAtomsRealized (K := K) q (.node (.halt, data) [])) :
    bindFP z (Noun.atom (leafAtomOf q data.2.pt.noun.leaf)) data.2.pt.noun := by
  have hex : ∃ k : ℕ, k < q ∧ (k : K) = data.2.pt.noun.leaf := hleaves
  rw [bindFP, GlobalCarryRecognizer.enc_atom]
  exact ComputeTable.FP.ext hatom.1 hatom.2 (leafAtomOf_cast hex).symm

end Nock.RedTeam.Batch524
