/-
  Nock/RedTeam/Batch515Thm54MemoryTreeBinds.lean

  **`MemoryTreeBinds` via `decode_fingerprint`.**

  `decode_fingerprint` plus `MemoryFingerprintStructure.of_rvtWithArity`
  give `enc z (decodeNoun q t) = memoryTreeRootFP t` from topology,
  shared seed, and halt-leaf atoms.  Parent
  `bindFP` is that equation.  `MemoryTreeBinds` still needs
  `BindMemRec` on `decodeMemoryRow`'s paper-`⊥` halves
  (`decodeMemoryRow_readRoot_child_is_atom0`).
-/
import Nock.NockVMROM.Thm54.HostileSkeletonDecoding
import Nock.NockVMROM.Thm54.NounRealization
import Nock.RedTeam.Batch342Thm54DecodedBinds
import Nock.RedTeam.Batch465Thm54DeployedRootLabelEqClaim
import Nock.RedTeam.Batch514Thm54RecordHalfJoin
import Nock.NockVMROM.Thm54.P8Core.Batch515Thm54MemoryTreeBinds

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch515

open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.RedTeam.Batch465
open Nock.RedTeam.Batch514

variable {K : Type} [Field K]

/-- Topology + shared seed + halt leaves ⇒ fingerprint equation. -/
theorem decode_fingerprint_of_topology {z : K} (hz : z ≠ 0) {q : ℕ}
    {t : NTree (MState × DTmem K)}
    (htop : RVTWithArity (Fmem (K := K)) t)
    (hseed : ∀ node, InTree t node → node.label.2.1.z = z)
    (hleaves : MemoryLeafAtomsRealized q t) :
    GlobalCarryRecognizer.enc z (decodeNoun q t) = memoryTreeRootFP t :=
  decode_fingerprint hz (MemoryFingerprintStructure.of_rvtWithArity z t htop hseed)
    hleaves

/-- Parent `bindFP` is `decode_fingerprint`. -/
theorem bindFP_parent_of_decode_fingerprint {z : K} (hz : z ≠ 0) {q : ℕ}
    {t : NTree (MState × DTmem K)}
    (hstructure : MemoryFingerprintStructure z t)
    (hleaves : MemoryLeafAtomsRealized q t) :
    bindFP z (decodeNoun q t) t.label.2.2.pt.noun := by
  simpa [bindFP, memoryTreeRootFP] using
    (decode_fingerprint hz hstructure hleaves).symm

/-- **Exact remaining statement** for `MemoryTreeBinds` after
    `decode_fingerprint`: `BindMemRec` on `decodeMemoryRow`, whose
    paper-`⊥` halves are still `atom 0`
    (`decodeMemoryRow_readRoot_child_is_atom0`). -/
def RemainingBindMemRec (z : K) (q : ℕ)
    (t : NTree (MState × DTmem K)) : Prop :=
  ∀ h : memoryMemRecKind (decodeMemoryRow (K := K) q t).state = .active,
    BindMemRec z ((decodeMemoryRow (K := K) q t).memoryRecord h)
      t.label.2.2.mem

theorem decode_fingerprint_is_a_theorem :
    True :=
  trivial

theorem memoryTreeBinds_still_blocked :
    "memory MemoryTreeBinds: RecordHalfJoin + decode_fingerprint (H1.4)" ∈
      bindsDropBlockersAfter :=
  recordHalfJoin_still_binds_blocker

theorem openAfterMemoryBinds_is_five :
    Nock.RedTeam.Batch509.openConjunctsAfterWrap.length = 5 :=
  Nock.RedTeam.Batch509.openConjunctsAfterWrap_length

theorem remainingBindMemRec_is_the_stop
    (q : ℕ) (data : DTmem K) (child : NTree (MState × DTmem K)) :
    ((decodeMemoryRow (K := K) q (.node (.read_root, data) [child])).memoryRecord
      (by simp [decodeMemoryRow, decodeMemoryRowIn_readRoot_state,
        memoryMemRecKind])).child = Noun.atom 0 := by
  simp [decodeMemoryRow, decodeMemoryRowIn, nounByFP, bfsForest_nil]

end Nock.RedTeam.Batch515

#print axioms Nock.RedTeam.Batch515.MemoryFingerprintStructure.of_InTree
#print axioms Nock.RedTeam.Batch515.decode_fingerprint_of_topology
#print axioms Nock.RedTeam.Batch515.bindFP_parent_of_decode_fingerprint
#print axioms Nock.RedTeam.Batch515.remainingBindMemRec_is_the_stop
