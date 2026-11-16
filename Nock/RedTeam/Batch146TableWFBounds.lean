/-
  Nock/RedTeam/Batch146TableWFBounds.lean

  Independent spec-redteam of honest-row `WF` bounds (`Nock/TableWFBounds.lean`).
  Different context from the prover.  Compiled evidence only.  FRAME-LOCK is
  not edited.  The consumed Thm 5.4 capstone
  `optimizedFullStrictNockVMROM_of_package` is not retouched.

  Paper frame (re-read at source): the paper.  SPEC-MAP 281 / 298.  FRAME-LOCK ~9387 M6.
-/
import Nock.TableWFBounds
import Nock.NockVMROM.Thm54.JointCoins
import Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch146

open Nock.TableWFBounds
open Nock.TableWFBounds.F97Witness
open Nock.ComputeTable (FP MemRec State)
open Nock.MemoryTable (MState)

/-! ## 1. Vacuity — live `F97Witness` rows inhabit the bound -/

/-- Live OP_5-unequal kernel has size `|K|²`.  the paper. -/
theorem b146_op5_bad_card :
    (badComputeAt (dummyCompute (K := F97) .s5 (FP.atomFP 1 0)
      (FP.atomFP 1 0) (FP.atomFP 1 1))).card
      = Fintype.card F97 * Fintype.card F97 :=
  F97Witness.op5_bad_card

/-- Zero compute coins fail `rlc5` on that live row.  the paper. -/
theorem b146_op5_zero_fails_rlc5 :
    ¬ rlc5Holds (0 : F97) 0 0
        (dummyCompute .s5 (FP.atomFP 1 0) (FP.atomFP 1 0) (FP.atomFP 1 1)) :=
  F97Witness.op5_zero_fails_rlc5

/-- OP_8 `size8` from `z`-powers once `z ≠ 0` (`one_ne_zero`, not `decide`). -/
theorem b146_op8_size8_of_z_ne :
    let pub := dummyCompute (K := F97) .s8 (FP.atomFP 1 0)
      (FP.atomFP 1 0) (FP.atomFP 1 0)
    pub.state = .s8 → pub.sf2_e.size ≠ 0 ∧ pub.s.size ≠ 0 :=
  F97Witness.op8_size8_of_z_ne 1 one_ne_zero

theorem b146_live_memory_bad_card :
    (badMemoryAt (dummyMemory (K := F97) .read_root MemRec.zero)).card
      = Fintype.card F97 :=
  F97Witness.live_memory_bad_card

/-- Zero `β` fails the live LogUp pole.  the paper. -/
theorem b146_live_memory_zero_beta_fails :
    ¬ poleHolds (0 : F97) 0 (dummyMemory .read_root MemRec.zero) :=
  F97Witness.live_memory_zero_beta_fails

/-! ## 2. Weakening/bundling — appendix `iff`s still take `WF` -/

/-- `Lem:equiv_compute` still threads `WF` on the exact biconditional. -/
theorem b146_equiv_compute_still_takes_wf {K : Type*} [Field K]
    (inp : Nock.ComputeTable.Inputs K) (pub : Nock.ComputeTable.Pub K)
    (dec : Nock.ComputeTable.Dec K) (wf : Nock.ComputeTable.WF inp pub) :
    (∃ ex, Nock.ComputeTable.RAPcomp inp pub dec ex) ↔
      Nock.ComputeTable.Vcomp inp pub dec :=
  Nock.ComputeTable.equiv_compute inp pub dec wf

/-- `Lem:equiv_mem` still threads `WF` on the exact biconditional. -/
theorem b146_equiv_mem_still_takes_wf {K : Type*} [Field K]
    (inp : Nock.MemoryTable.Inputs K) (p : Nock.MemoryTable.Pub K)
    (wf : Nock.MemoryTable.WF inp p) :
    (∃ g, Nock.MemoryTable.RAPmem inp p g) ↔ Nock.MemoryTable.Vmem inp p :=
  Nock.MemoryTable.equiv_mem inp p wf

/-- Honest `V_comp` plus assembled `WF` still inhabits `RAP_comp` through
    the existing `iff`.  the paper. -/
theorem b146_honest_compute_inhabits_RAP {K : Type*} [Field K]
    (inp : Nock.ComputeTable.Inputs K) (pub : Nock.ComputeTable.Pub K)
    (dec : Nock.ComputeTable.Dec K) (wf : Nock.ComputeTable.WF inp pub)
    (hv : Nock.ComputeTable.Vcomp inp pub dec) :
    ∃ ex, Nock.ComputeTable.RAPcomp inp pub dec ex :=
  honest_compute_inhabits_RAP inp pub dec wf hv

/-- Honest `V_mem` plus assembled `WF` still inhabits `RAP_mem` through
    the existing `iff`.  the paper. -/
theorem b146_honest_memory_inhabits_RAP {K : Type*} [Field K]
    (inp : Nock.MemoryTable.Inputs K) (p : Nock.MemoryTable.Pub K)
    (wf : Nock.MemoryTable.WF inp p) (hv : Nock.MemoryTable.Vmem inp p) :
    ∃ g, Nock.MemoryTable.RAPmem inp p g :=
  honest_memory_inhabits_RAP inp p wf hv

/-! ## 3. Definitional — sizes are `z`-powers; bound is over `(a,b,c,β,γ)` -/

/-- `HonestSize` is definitionally a `z`-power, not a Schwartz–Zippel event. -/
theorem b146_honestSize_is_z_pow {K : Type*} [Field K] {z : K}
    {fp : FP K} :
    HonestSize z fp ↔ ∃ n : ℕ, fp.size = z ^ n :=
  Iff.rfl

/-- Honest-row bound is stated over `WFJointCoins`.  the paper. -/
theorem b146_honest_row_prob_ge {n l : ℕ}
    (crows : Fin n → Nock.ComputeTable.Pub F97)
    (mrows : Fin l → Nock.MemoryTable.Pub F97) :
    (1 : ℚ) - ((badJoint crows mrows).card : ℚ)
        / (Fintype.card (WFJointCoins F97) : ℚ)
      ≥ 1 - ((n + l : ℕ) : ℚ) / (Fintype.card F97 : ℚ) :=
  honest_row_prob_ge crows mrows

/-- Five-fold coin space `|K|^5`.  the paper. -/
theorem b146_wfJointCoins_card_F97 :
    Fintype.card (WFJointCoins F97) = 97 ^ 5 := by
  rw [card_wfJointCoins, ZMod.card]

/-! ## 4. -/

theorem b146_p8_jointCoins_card_F97 :
    Fintype.card (Nock.NockVMROM.Thm54.JointCoins F97) = 97 ^ 4 := by
  change Fintype.card ((F97 × F97) × (F97 × F97)) = 97 ^ 4
  simp [Fintype.card_prod, ZMod.card]

theorem b146_wfJointCoins_ne_p8_jointCoins :
    Fintype.card (WFJointCoins F97)
      ≠ Fintype.card (Nock.NockVMROM.Thm54.JointCoins F97) := by
  rw [b146_wfJointCoins_card_F97, b146_p8_jointCoins_card_F97]
  decide

/-! Consumed Thm 5.4 field is still algebraic `Language` membership of
    `stmtOfExact`.  Type has no `JointCoins` / `Accepts`.  Capstone not
    retouched.  the paper. -/
noncomputable section

open scoped Classical
open Nock Nock.Noun
open Framework Framework.Thm54
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.EqualityOperandCensus
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusCommitment
open Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
open Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
open Nock.NockVMROM.Thm54.DistinctCensusFold2
open Nock.NockVMROM.Thm54.DistinctCensusWholeJoint
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

local instance prime97b146 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97b146 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
variable (haxR : FormRAxisBound (packageR hfirstD).optimized.sampled
    (packageR hfirstD).optimized.basis)
variable (hbasisR : FormRBasis (packageR hfirstD).optimized.basis)
variable (hwidthR : FormRWidth OptimizedStrictNonterminalConcrete.F97)
include haxR hbasisR hwidthR
variable (hrootAt : ∀ a g : K97cubic,
  (packageR hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
variable (hrootAtQ : ∀ a g : K97cubic,
  (packageQ hfirstD).strategy.RootAxisBoundaryAt
    (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
include hfirstD
include hrootAt
include hrootAtQ

/-- Independent wrap of the consumed field.  Capstone not retouched. -/
theorem b146_consumed_perfect_completeness_holds :
    Language
      (Tag OptimizedStrictNonterminalConcrete.F97 K97cubic
        (packageR hfirstD).objects.cfg.challenges.α
        (packageR hfirstD).objects.cfg.challenges.β (packageR hfirstD).objects.cfg.Ksz)
      (stmtOfExact (packageR hfirstD).objects.cfg (packageR hfirstD).objects.exec) :=
  DistinctCensusCompletenessLayers.consumed_perfect_completeness_holds
    hfirstD haxR hbasisR hwidthR hrootAt hrootAtQ

end

#print axioms b146_op5_bad_card
#print axioms b146_op5_zero_fails_rlc5
#print axioms b146_op8_size8_of_z_ne
#print axioms b146_live_memory_bad_card
#print axioms b146_live_memory_zero_beta_fails
#print axioms b146_equiv_compute_still_takes_wf
#print axioms b146_equiv_mem_still_takes_wf
#print axioms b146_honest_compute_inhabits_RAP
#print axioms b146_honest_memory_inhabits_RAP
#print axioms b146_honestSize_is_z_pow
#print axioms b146_honest_row_prob_ge
#print axioms b146_wfJointCoins_card_F97
#print axioms b146_p8_jointCoins_card_F97
#print axioms b146_wfJointCoins_ne_p8_jointCoins
#print axioms b146_consumed_perfect_completeness_holds
#print axioms Nock.ComputeTable.equiv_compute
#print axioms Nock.MemoryTable.equiv_mem
#print axioms honest_row_prob_ge
#print axioms F97Witness.op5_bad_card
#print axioms F97Witness.op8_size8_of_z_ne
#print axioms Nock.NockVMROM.Thm54.DistinctCensusCompletenessLayers.consumed_perfect_completeness_holds

end Nock.RedTeam.Batch146
