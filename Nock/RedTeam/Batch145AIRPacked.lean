/-
  Nock/RedTeam/Batch145AIRPacked.lean

  Independent spec-redteam of packed compute AIR (`Nock/AIRPacked.lean`).
  Different context from the prover.  Compiled evidence only.  Production
  `computeAIR` (526, histogram 10/472/31/13) is not swapped.  Consumed capstones for THIS item:
  `packed_iff_atomic`, `computeAIRPacked_sound`, `computeAIRPacked_sound_free`.
-/
import Nock.AIRPacked
import Nock.Counts
import Nock.NockVMROM.Thm54.TraceGen.Op1AIR

namespace Nock.RedTeam.Batch145

open Nock.Reified
open Nock.ComputeTable
open Nock.NockVMROM.Thm54.TraceGen.Op1

/-! ## 1. Vacuity — packed soundness is inhabited at a real field

  The Op1AIR row (`z = 8` over `ZMod 97`) does. -/

/-- Packed constraints vanish on the honest OP_1 environment.  the paper. -/
theorem b145_op1_computeAIRPacked_zero :
    ∀ c ∈ computeAIRPacked.constraints,
      c.expr.eval (computeEnvFull op1Inp (opSel op1Pub.state) op1Pub op1Dec op1Ex) = 0 :=
  (computeAIRPacked_sound op1Inp op1Pub op1Dec op1Ex).mpr ⟨op1_rapcomp, op1_z_ne_zero⟩

/-! ## 2. Weakening/bundling — `packed_iff_atomic` threads the same objects -/

/-- Same `inp/pub/dec/ex` and the same `st` on both sides.  the paper. -/
theorem b145_packed_iff_atomic_threads {K : Type*} [Field K]
    (inp : Inputs K) (pub : Pub K) (dec : Dec K) (ex : Extra K) (st : State) :
    (∀ e ∈ allPacked, e.eval (computeEnvFull inp (opSel (K := K) st) pub dec ex) = 0)
      ↔ (∀ e ∈ memBlkExprs st ++ evalRExprs st,
            e.eval (computeEnvFull inp (opSel (K := K) st) pub dec ex) = 0) :=
  packed_iff_atomic inp pub dec ex st

/-! ## 3. Definitional checks vs `tab:V_comp_equality` / combined fold / ln -/

/-- FLAG `[combined-op8-factor]`: EC.8.1 at `:2000` keeps `input_subject.size`.
    Display `:2016` drops it.  Lean fold retains the 3-factor gate. -/
theorem b145_combinedPacked_op8_keeps_subject_size {K : Type*} [Field K]
    (inp : Inputs K) (pub : Pub K) (dec : Dec K) (ex : Extra K) :
    combinedPackedExpr.eval (computeEnvFull inp (opSel (K := K) .s8) pub dec ex)
      = pub.sf2_e.size * pub.s.size * ex.invGen - 1 := by
  convert combinedPacked_eval inp pub dec ex State.s8

/-- Combined fold is `Σ op_k · (G_k − 1) = 0`, not `Σ G = 1`.  Inactive OP_1
    evaluates to 0.  the paper. -/
theorem b145_combinedPacked_inactive_s1_is_zero {K : Type*} [Field K]
    (inp : Inputs K) (pub : Pub K) (dec : Dec K) (ex : Extra K) :
    combinedPackedExpr.eval (computeEnvFull inp (opSel (K := K) .s1) pub dec ex) = 0 := by
  convert combinedPacked_eval inp pub dec ex State.s1

/-- Packed extras at OP_8 are the 3-factor EC.8.1 gate.  the paper. -/
theorem b145_extraPacked_op8_is_three_factor {K : Type*} [Field K]
    (inp : Inputs K) (pub : Pub K) (dec : Dec K) (ex : Extra K) :
    (∀ e ∈ extraPacked,
        e.eval (computeEnvFull inp (opSel (K := K) .s8) pub dec ex) = 0)
      ↔ pub.sf2_e.size * pub.s.size * ex.invGen = 1 := by
  convert extraPacked_zero inp pub dec ex State.s8

/-- Paper ln display `:1886` omits `op_11`.  Algorithm `:1741` gives cons 1 access.
    Lean places cons in the `α` group. -/
theorem b145_lnPacked_cons_in_alpha_group {K : Type*} [Field K]
    (inp : Inputs K) (pub : Pub K) (dec : Dec K) (ex : Extra K) :
    lnPackedExpr.eval (computeEnvFull inp (opSel (K := K) .cons) pub dec ex)
      = pub.ln - pub.ln_prev * inp.α := by
  convert lnPacked_eval inp pub dec ex State.cons

/-- OP_1 is in the same `α` group as cons.  the paper. -/
theorem b145_lnPacked_s1_in_alpha_group {K : Type*} [Field K]
    (inp : Inputs K) (pub : Pub K) (dec : Dec K) (ex : Extra K) :
    lnPackedExpr.eval (computeEnvFull inp (opSel (K := K) .s1) pub dec ex)
      = pub.ln - pub.ln_prev * inp.α := by
  convert lnPacked_eval inp pub dec ex State.s1

/-! ## 4. Wrong layer — production atomic AIR is still 526; packed is the sibling 93.

  Packing does not replace `optimizedFullStrictNockVMROM_of_package`.
  `computeAIRchained` stays 527 = atomic 526 + 1.  the paper. -/

theorem b145_atomic_still_526 : computeAIR.constraints.length = 526 :=
  computeAIR_num_constraints

theorem b145_packed_is_93 : computeAIRPacked.constraints.length = 93 :=
  computeAIRPacked_num_constraints

theorem b145_chained_still_527 : Trans.computeAIRchained.constraints.length = 527 :=
  Trans.computeAIRchained_num_constraints

/-- Production histogram 10/472/31/13 is untouched.  the paper. -/
theorem b145_atomic_hist_unchanged :
    computeAIR.constraints.countP (fun c => c.degree == 1) = 10 ∧
    computeAIR.constraints.countP (fun c => c.degree == 2) = 472 ∧
    computeAIR.constraints.countP (fun c => c.degree == 3) = 31 ∧
    computeAIR.constraints.countP (fun c => c.degree == 4) = 13 :=
  ⟨computeAIR_deg1, computeAIR_deg2, computeAIR_deg3, computeAIR_deg4⟩

/-- Packed per-row block is 66 (= eval 32 + extra 11 + mem 23).  the paper. -/
theorem b145_allPacked_length : allPacked.length = 66 := rfl

/-- Prefix 27 + packed 66 = 93.  the paper. -/
theorem b145_prefix_plus_packed : 27 + 66 = 93 := rfl

#print axioms b145_op1_computeAIRPacked_zero
#print axioms b145_packed_iff_atomic_threads
#print axioms b145_combinedPacked_op8_keeps_subject_size
#print axioms b145_combinedPacked_inactive_s1_is_zero
#print axioms b145_extraPacked_op8_is_three_factor
#print axioms b145_lnPacked_cons_in_alpha_group
#print axioms b145_lnPacked_s1_in_alpha_group
#print axioms b145_atomic_still_526
#print axioms b145_packed_is_93
#print axioms b145_chained_still_527
#print axioms b145_atomic_hist_unchanged
#print axioms b145_allPacked_length
#print axioms b145_prefix_plus_packed
#print axioms packed_iff_atomic
#print axioms computeAIRPacked_sound
#print axioms computeAIRPacked_sound_free
#print axioms computeAIRPacked_num_constraints
#print axioms computeAIRPacked_maxDegree
#print axioms packed_fewer_constraints_than_atomic

end Nock.RedTeam.Batch145
