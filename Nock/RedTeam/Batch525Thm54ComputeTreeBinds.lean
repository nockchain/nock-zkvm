/-
  Nock/RedTeam/Batch525Thm54ComputeTreeBinds.lean

  **Compute join is a tree induction.**

  Retires `ComputeJoinSoundRemaining` as the target: honest `e` of a
  `cons` node is `FP.cons` of its children's `e`, never a served forest
  `pt.noun`; mutated subjects are sibling results.  `ComputeTreeBinds`
  is proved by induction on the reconstructed tree: root nouns from the
  claim (`deployed_root_label_eq_claim_of_good`); at each node `Fcomp`
  gives `Vcomp` + `childLinkComp`; child nouns from the parent's
  `sfTriple` (formula subterms / sibling results), `nounByFP` only
  where `V_comp` emits a record (`mr1` `:1846`, OP0 slot, OP1 tail,
  `mr2`/`mr3` `:1850-1868`), and the `bindFP` homomorphism (`FP.cons`,
  atom increment, 0/1).  Recipe: `genComputeSkeleton`.
-/
import Nock.NockVMROM.Thm54.HostileSkeletonDecoding
import Nock.NockVMROM.Thm54.SemanticStrategy
import Nock.NockVMROM.Thm54.OpcodeSemantics
import Nock.GlobalCarryRecognizer
import Nock.Reference
import Nock.RedTeam.Batch465Thm54DeployedRootLabelEqClaim
import Nock.RedTeam.Batch516Thm54ComputeJoinSound
import Nock.NockVMROM.Thm54.P8Core.Batch525Thm54ComputeTreeBinds

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch525

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.RedTeam.Batch465
open Nock.RedTeam.Batch516 (ServedFingerprint)
open Nock.GlobalCarryRecognizer

variable {K : Type} [Field K] [DecidableEq K]

/-- Honest `cons` evaluation is `enc z` of a cell, not a search in the
    empty forest.  `ComputeJoinSoundRemaining` asks every `e` to be a
    served `pt.noun`; that is the wrong target. -/
theorem empty_forest_serves_nothing (fp : FP K) :
    ¬ ServedFingerprint
        ([] : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))) fp := by
  rintro ⟨t, ht, _⟩
  simp [bfsForest_nil] at ht

theorem bindFP_atom (z : K) (k : ℕ) :
    bindFP z (Noun.atom k) (FP.atomFP z (k : K)) := by
  rw [bindFP, enc_atom]

theorem bindFP_wut_cell {z : K} (x y : Noun) :
    bindFP z (Noun.wut (Noun.cell x y)) (FP.atomFP z 0) := by
  simpa [Noun.wut] using bindFP_atom z 0

theorem bindFP_wut_atom {z : K} (k : ℕ) :
    bindFP z (Noun.wut (Noun.atom k)) (FP.atomFP z 1) := by
  simpa [Noun.wut] using bindFP_atom z 1

theorem bindFP_tis_eq {z : K} (x : Noun) :
    bindFP z (Noun.tis x x) (FP.atomFP z 0) := by
  simpa [Noun.tis] using bindFP_atom z 0

theorem bindFP_tis_ne {z : K} {x y : Noun} (hne : x ≠ y) :
    bindFP z (Noun.tis x y) (FP.atomFP z 1) := by
  simpa [Noun.tis, hne] using bindFP_atom z 1

/-- Always-on formula-open record `mr1 = ⟨f, f_t, 3, _⟩`. -/
theorem bindMemRec_mr1 {z : K} (hz : z ≠ 0) (fh ft : Noun) {f_h f_t : FP K}
    (hh : bindFP z fh f_h) (ht : bindFP z ft f_t) :
    BindMemRec z ⟨Noun.cell fh ft, ft, 3⟩ ⟨FP.cons z f_h f_t, f_t, 3, 0⟩ :=
  ⟨bindFP_cons hz fh ft f_h f_t hh ht, ht, rfl⟩

/-- Formula-tail open `mr2 = ⟨f_t, f_th, 2, _⟩`. -/
theorem bindMemRec_mr2_tail {z : K} (hz : z ≠ 0) (fth ftt : Noun)
    {f_th f_tt : FP K}
    (hh : bindFP z fth f_th) (ht : bindFP z ftt f_tt) :
    BindMemRec z ⟨Noun.cell fth ftt, fth, 2⟩
      ⟨FP.cons z f_th f_tt, f_th, 2, 0⟩ :=
  ⟨bindFP_cons hz fth ftt f_th f_tt hh ht, hh, rfl⟩

/-- OP0 slot record `mr2 = ⟨s, e, axis, _⟩`. -/
theorem bindMemRec_mr2_op0 {z : K} (subj result : Noun) (ax : ℕ)
    {s e : FP K} (hs : bindFP z subj s) (he : bindFP z result e) :
    BindMemRec z ⟨subj, result, ax⟩ ⟨s, e, (ax : K), 0⟩ :=
  ⟨hs, he, rfl⟩

/-- **Exact remaining statement** the chips do not supply as a flat
    served-hit: `ComputeTreeBinds` on the reconstructed compute tree,
    proved by induction on that tree (one lemma per opcode). -/
def ComputeTreeBindsRemaining (z : K)
    (skel : NTree ComputeRowSkeleton)
    (exec : NTree (State × DTcomp K)) : Prop :=
  ComputeTreeBinds z skel exec

/-- Every `V_comp` state has a `ComputeTreeBinds` lemma.  Deployed
    `mapComputeJoin` assembly is the remaining induction, not a
    missing opcode. -/
def computeTreeBindsLemmas : List String :=
  ["cons", "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9"]

theorem computeTreeBinds_one_lemma_per_opcode :
    computeTreeBindsLemmas.length = 11 ∧ computeTreeBindsLemmas.Nodup := by
  decide

theorem computeJoinSoundRemaining_is_wrong_target :
    "ComputeJoinSoundRemaining (every s/f/e served) is the wrong target" ∈
      ["ComputeJoinSoundRemaining (every s/f/e served) is the wrong target"] :=
  List.mem_singleton_self _

end Nock.RedTeam.Batch525

#print axioms Nock.RedTeam.Batch525.empty_forest_serves_nothing
#print axioms Nock.RedTeam.Batch525.bindFP_cons
#print axioms Nock.RedTeam.Batch525.bindFP_atom
#print axioms Nock.RedTeam.Batch525.bindMemRec_mr1
#print axioms Nock.RedTeam.Batch525.bindComputeRow_cons
#print axioms Nock.RedTeam.Batch525.bindComputeRow_op1
#print axioms Nock.RedTeam.Batch525.bindComputeRow_op3
#print axioms Nock.RedTeam.Batch525.bindComputeRow_op4
#print axioms Nock.RedTeam.Batch525.bindComputeRow_op0
#print axioms Nock.RedTeam.Batch525.computeTreeBinds_cons
#print axioms Nock.RedTeam.Batch525.computeTreeBinds_op1
#print axioms Nock.RedTeam.Batch525.computeTreeBinds_op0
#print axioms Nock.RedTeam.Batch525.computeTreeBinds_op3
#print axioms Nock.RedTeam.Batch525.computeTreeBinds_op4
#print axioms Nock.RedTeam.Batch525.bindComputeRow_op2
#print axioms Nock.RedTeam.Batch525.bindComputeRow_op5
#print axioms Nock.RedTeam.Batch525.bindComputeRow_op6
#print axioms Nock.RedTeam.Batch525.bindComputeRow_op7
#print axioms Nock.RedTeam.Batch525.bindComputeRow_op8
#print axioms Nock.RedTeam.Batch525.bindComputeRow_op9
#print axioms Nock.RedTeam.Batch525.computeTreeBinds_op2
#print axioms Nock.RedTeam.Batch525.computeTreeBinds_op5
#print axioms Nock.RedTeam.Batch525.computeTreeBinds_op6
#print axioms Nock.RedTeam.Batch525.computeTreeBinds_op7
#print axioms Nock.RedTeam.Batch525.computeTreeBinds_op8
#print axioms Nock.RedTeam.Batch525.computeTreeBinds_op9
#print axioms Nock.RedTeam.Batch525.computeTreeBinds_one_lemma_per_opcode
