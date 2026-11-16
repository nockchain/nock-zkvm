import Nock.NockVMROM.Thm54.VclL.Compute.CompTreeVCL
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign
import Nock.NockVMROM.Thm54.Unhosted309Events

/-!
# CF-A : `CompSoundnessVCL` — the compute soundness family at VCL

.

`compSoundnessVCL F K hC S : CompSoundnessFamily F K K K RV.KeyVCL frameVCL hC S (tableVCLE hC) 3
(recordViewVCL …) (seedSpecCF K) (ioCF K)` — every SOUNDNESS field is proved:

* `tree := treeV` (`treeRound := 2`), `shape := shapeV`, `keyOf := keyOfQ7`, `recKey := recKeyQ7'`
  (stride-2 carrier, `recKey_s0'`), `axB0 := axB0Q7`;
* `inlineRecords := 0` (`inline_*` vacuous), `summands := summandsQ7`,
  `node_records := node_records_CF`, `root_binds := root_binds_CF`.

**Instance level (labelled).**  The family is at the TEST instance `Kio = Kfp = K`,
`Z := seedSpecCF` (`seed χ = χ 2`), `I := ioCF K` (`(χ4, χ5)`): the compiled chip's records live in
`K`, so it is not parametric in `Kio`/`Kfp`; the tower instance is after TWD phase 2.

**Honest fields: PLACEHOLDER (`Honest := PEmpty`).**  The honest side (`honestV`, `honestQ`,
`honest_accepted`, …) is LD2p's; with an empty `Honest` the fields are vacuous.  This family proves
SOUNDNESS only and must not be read as completeness.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace CompSoundnessVCL

open Nock Nock.Walk Nock.Reified Nock.Framework Nock.Framework.Reify Module Nock.ComputeTable
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7
open Nock.NockVMROM.Thm54.VclL.Compute.CompChipVCL
open Nock.NockVMROM.Thm54.VclL.Compute.CompTreeVCL
open scoped Polynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 300000

noncomputable section

/-- The NPR seed of the test instance: coin `2` (`frameVCL`, sampled after block 0). -/
def seedSpecCF (K : Type) : SeedSpec frameVCL K K where
  seed := fun χ => χ ⟨2, by decide⟩
  dep := {(⟨2, by decide⟩ : Fin frameVCL.n)}
  readsOn := fun χ χ' h => h _ (Finset.mem_singleton_self _)
  round0 := fun i hi => by
    rw [Finset.mem_singleton] at hi
    rw [hi]; show frameVCL.sampledAfter ⟨2, by decide⟩ = 0; decide
  inj := fun χ χ' h i hi => by
    rw [Finset.mem_singleton] at hi
    rw [hi]; exact h

section family
variable (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [CharP K (ringChar K)] [Fintype F] [DecidableEq F] (hC : ℕ) (S : MemShape)

/-- **`CompSoundnessVCL`** (soundness fields proved; honest fields placeholder, `Honest := PEmpty`). -/
def compSoundnessVCL :
    CompSoundnessFamily F K K K RV.KeyVCL frameVCL hC S (tableVCLE hC) 3 (m := RV.mVCL)
      (RV.recordViewVCL F K K (tableVCLE hC) S hC) (seedSpecCF K) (ioCF K) where
  Msg0 := ℕ → F
  chip := fun V x ρ χ => chipCF V x ρ χ
  chip_width := fun V x ρ χ => chipCF_width V x ρ χ
  reqBound := reqBoundCF
  reqFacts := fun V x ρ χ Q h => reqFactsCF V x ρ χ Q h
  reqFacts_length := fun V x ρ χ Q h a => reqFactsCF_length V x ρ χ Q h a
  reqRecords := fun V x Q χ => reqRecordsCF V x Q χ
  recRound := 1
  recRound_le_io := fun i hi => by
    simp only [ioCF, IOCoinSpec.ofPair, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> decide
  reqRecords_round := fun V x Q Q' χ χ' hQ _ => by
    funext a
    exact reqRecsQ7_round1 V _ _ _ _ Q Q' (fun j hj => hQ j hj) a
  reqFacts_records := fun V x ρ χ Q h a => reqFactsCF_records V x ρ χ Q h a
  shape := fun V _ b => shapeV V b
  shape_size := fun V _ b => shapeV_size_le V b
  tree := fun V x Q χ => treeV V (chalVQ7 V.basis χ) (pubVQ7 V.basis V.claim x χ) Q
  treeRound := 2
  tree_round := fun V x Q Q' χ χ' hQ hχ => by
    have hs : ∀ i : Fin frameVCL.n, frameVCL.sampledAfter i < 2 := by decide
    have h1 : χ = χ' := funext fun i => hχ i (hs i)
    have h2 : Q = Q' := funext fun j => hQ j (colRoundVCLE_le_two j)
    subst h1; subst h2; rfl
  tree_shape := fun V x Q χ => treeV_shape V _ _ Q
  axB0 := fun V _ b _ k => axB0Q7 V b k
  keyOf := fun V _ b st k => keyOfQ7 V b st k
  recKey := fun V _ b st S' j => recKeyQ7' V b st S' j
  recKey_s0 := fun V _ b S' => recKey_s0' V b S'
  inlineRecords := fun _ => 0
  inline_not_read := fun st j hj => absurd hj (Nat.not_lt_zero _)
  inlinePairs := fun _ _ _ => []
  inlinePairCount := 0
  inlinePairs_length := fun _ _ _ => le_rfl
  summands := fun V _ => SummandsQ7.summandsQ7 V
  node_records := fun V x ρ χ Q h Qm hout u hu j _ hj =>
    node_records_CF V x ρ χ Q h Qm hout u hu j hj
  inline_records := fun V x ρ χ Q h Qm hout u hu j hj => absurd hj (Nat.not_lt_zero _)
  root_binds := fun V x ρ χ Q h Qm hout => root_binds_CF V x ρ χ Q h Qm hout
  Honest := PEmpty
  honestV := fun H => H.elim
  honestMsg0 := fun H => H.elim
  honestReq := fun H => H.elim
  honestQ := fun H => H.elim
  honest_staged := fun H => H.elim
  honestBad := fun H => H.elim
  honest_accepted := fun H => H.elim

end family

end

end CompSoundnessVCL
end VclL.Compute
end Nock.NockVMROM.Thm54
