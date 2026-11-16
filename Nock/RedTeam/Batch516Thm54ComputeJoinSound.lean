/-
  Nock/RedTeam/Batch516Thm54ComputeJoinSound.lean

  **`ComputeJoinSound` / `decoded_binds_compute`.**

  `nounByFP` reads a forest noun whose `pt.noun` equals the compute
  fingerprint.  On a hit, `decode_fingerprint` gives `bindFP`
  (`bindFP_of_nounByFP_hit`).  `ComputeJoinSound` still needs every
  compute `s`/`f`/`e` (and active `dec` / `mr` slots) to be a served
  forest `pt.noun` (`ServedFingerprint` / `ComputeJoinSoundRemaining`).

  Does **not** depend on `decodeMemoryRow`'s paper-`⊥` halves.
-/
import Nock.NockVMROM.Thm54.HostileSkeletonDecoding
import Nock.RedTeam.Batch342Thm54DecodedBinds
import Nock.RedTeam.Batch465Thm54DeployedRootLabelEqClaim
import Nock.RedTeam.Batch515Thm54MemoryTreeBinds
import Nock.NockVMROM.Thm54.P8Core.Batch516Thm54ComputeJoinSound

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Classical

namespace Nock.RedTeam.Batch516

open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.RedTeam.Batch465
open Nock.RedTeam.Batch515

variable {K : Type} [Field K] [DecidableEq K]

noncomputable section

/-- Same `find?` as `StrategyOfTraces.nounByFP`, without the package argument. -/
def nounByFP (q : ℕ)
    (forest : List (NTree (MState × DTmem K))) (fp : FP K) : Noun :=
  match (bfsForest forest).find? (fun t => decide (t.label.2.2.pt.noun = fp)) with
  | some t => decodeNoun q t
  | none => Noun.atom 0

theorem nounByFP_of_served {q : ℕ}
    {forest : List (NTree (MState × DTmem K))} {fp : FP K}
    (h : ServedFingerprint forest fp) :
    ∃ t ∈ bfsForest forest,
      t.label.2.2.pt.noun = fp ∧ nounByFP q forest fp = decodeNoun q t := by
  unfold nounByFP
  cases hfind :
      (bfsForest forest).find? (fun t => decide (t.label.2.2.pt.noun = fp)) with
  | none =>
    obtain ⟨t, ht, hfp⟩ := h
    have hnone := List.find?_eq_none.mp hfind t ht
    simp at hnone
    exact (hnone hfp).elim
  | some t =>
    refine ⟨t, List.mem_of_find?_eq_some hfind, ?_, rfl⟩
    have hp := List.find?_some hfind
    simpa using hp

/-- Hit + fingerprint structure ⇒ `bindFP` of `nounByFP`. -/
theorem bindFP_of_nounByFP_hit {z : K} (hz : z ≠ 0) {q : ℕ}
    {forest : List (NTree (MState × DTmem K))} {fp : FP K}
    (hstruct : ∀ t ∈ bfsForest forest, MemoryFingerprintStructure z t)
    (hleaves : ∀ t ∈ bfsForest forest, MemoryLeafAtomsRealized q t)
    (hhit : ServedFingerprint forest fp) :
    bindFP z (nounByFP q forest fp) fp := by
  obtain ⟨t, ht, hfp, hnoun⟩ := nounByFP_of_served (q := q) hhit
  rw [hnoun, bindFP, ← hfp]
  exact (decode_fingerprint hz (hstruct t ht) (hleaves t ht)).symm

/-- **Exact remaining statement** the chips do not supply: every
    compute-row `s`/`f`/`e` equals some forest `pt.noun`. -/
def ComputeJoinSoundRemaining
    (forest : List (NTree (MState × DTmem K)))
    (tree : NTree (State × DTcomp K)) : Prop :=
  ∀ node, InTree tree node →
    ServedFingerprint forest node.label.2.2.1.s ∧
      ServedFingerprint forest node.label.2.2.1.f ∧
        ServedFingerprint forest node.label.2.2.1.e

theorem computeJoin_still_blocked :
    "compute BindComputeRow rows: decoded_binds_compute needs ComputeJoinSound (H1.4 join)" ∈
      bindsDropBlockersAfter := by
  decide

theorem openAfterComputeJoin_is_five :
    Nock.RedTeam.Batch509.openConjunctsAfterWrap.length = 5 :=
  Nock.RedTeam.Batch509.openConjunctsAfterWrap_length

end

end Nock.RedTeam.Batch516

#print axioms Nock.RedTeam.Batch516.nounByFP_of_served
#print axioms Nock.RedTeam.Batch516.bindFP_of_nounByFP_hit
#print axioms Nock.RedTeam.Batch516.computeJoin_still_blocked
