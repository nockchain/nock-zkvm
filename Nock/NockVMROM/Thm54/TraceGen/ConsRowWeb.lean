/-
  Nock/NockVMROM/Thm54/TraceGen/ConsRowWeb.lean

  The per-row `Vcomp` acceptance,
  genericity (`WF`), whole-tree row acceptance, and arity-3 `Fcomp` topology of the three-row
  BRANCHING compute tree of `*[0 [[1 5] [1 6]]] = [5 6]` over `K = ZMod 97`, seed `z = 8`, `α = 4`.

  NEW vs OP1: the root is the `.cons` autocons opcode.  Its `Vcomp`
  acceptance is genuinely new — the `.cons` branch of `SVhead` demands a CELL head rather than a numeric atom head, its `memBlk` uses the
  single-`α` line recurrence, and its `evalV` is the two-branch
  autocons `e = FP.cons z sf1_e sf2_e`.  The compute tree is BRANCHING for the
  first time, so `Fcomp` carries a genuine fanout-2 `childLinkComp` tying each `OP_1` child's
  `(s, f, e)` to the parent `.cons` row's subformula slot.

  This is the compute half of the eventual `ExactExecutionSemanticData.rowAccepted` and
  `language.compute_topology`; the thirteen-row memory `Vmem`/LogUp web and the semantic IO
  preimage remain the open memory-CORE obligation (see the module header of `ConsSkeleton`).
-/
import Nock.NockVMROM.Thm54.TraceGen.ConsConfig
import Nock.NockVMROM.Thm54.TraceGen.ConsSemanticData
import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.NockVMROM.Thm54.ExactTraversal

namespace Nock.NockVMROM.Thm54.TraceGen.ConsConfig

open Nock Nock.Walk Nock.MemoryTable Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen.ConsSkeleton

noncomputable section

/-! ## The autocons head is a genuine cell -/

/-- The `.cons` row's formula head `[1 5]` is a cell, so its Dyck fingerprint is nonzero: with
`z = 8`, `(enc [1 5]).dyck = z·0 + z²·z⁻¹ + z²·0 = z = 8 ≠ 0`. -/
theorem consHead_dyck_ne : consDec.f_h.dyck ≠ (0 : F) := by
  have hval : consDec.f_h.dyck = seedZ := by
    show (GlobalCarryRecognizer.enc seedZ (Noun.cell op1Head leftResult)).dyck = seedZ
    rw [GlobalCarryRecognizer.enc_cons seedZ_ne_zero,
      show op1Head = Noun.atom 1 from rfl, show leftResult = Noun.atom 5 from rfl,
      GlobalCarryRecognizer.enc_atom, GlobalCarryRecognizer.enc_atom]
    simp only [ComputeTable.FP.cons, ComputeTable.FP.atomFP_dyck, ComputeTable.FP.atomFP_size,
      mul_zero, add_zero, zero_add]
    rw [mul_assoc, mul_inv_cancel₀ seedZ_ne_zero, mul_one]
  rw [hval]; exact seedZ_ne_zero

/-! ## The three compute rows are accepted by `V_comp` -/

/-- The `.cons` autocons row is accepted by the algorithmic compute verifier. -/
theorem cons_accepts : Vcomp compInputs consPub consDec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero leftFormula rightFormula
  · ext <;> norm_num [consPub, recCons, consDec, compInputs, seedZ, alphaA]
  · show SVhead compInputs consPub consDec
    unfold SVhead
    rw [if_pos (show consPub.state = State.cons from rfl)]
    exact consHead_dyck_ne
  · exact ⟨rfl, rfl, by simp [consPub, compInputs]⟩
  · exact ⟨rfl, rfl, rfl, rfl,
      GlobalCarryRecognizer.enc_cons seedZ_ne_zero leftResult rightResult, rfl, rfl, rfl⟩

/-- The left `OP_1` child row `*[0 [1 5]] = 5` is accepted. -/
theorem op1L_accepts : Vcomp compInputs op1LPub (op1DecOf leftResult) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op1Head leftResult
  · ext <;> norm_num [op1LPub, op1PubOf, recL, op1DecOf, compInputs, seedZ, alphaA, pow_two]
  · simp [SVhead, headAtom, op1LPub, op1PubOf, op1DecOf, enc,
      show op1Head = Noun.atom 1 from rfl, GlobalCarryRecognizer.enc_atom, State.toNat,
      compInputs, seedZ]
  · exact ⟨rfl, rfl, by simp [op1LPub, op1PubOf, compInputs]⟩
  · exact ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- The right `OP_1` child row `*[0 [1 6]] = 6` is accepted. -/
theorem op1R_accepts : Vcomp compInputs op1RPub (op1DecOf rightResult) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op1Head rightResult
  · ext <;> norm_num [op1RPub, op1PubOf, recR, op1DecOf, compInputs, seedZ, alphaA, pow_two,
      pow_succ]
  · simp [SVhead, headAtom, op1RPub, op1PubOf, op1DecOf, enc,
      show op1Head = Noun.atom 1 from rfl, GlobalCarryRecognizer.enc_atom, State.toNat,
      compInputs, seedZ]
  · exact ⟨rfl, rfl, by simp [op1RPub, op1PubOf, compInputs, pow_succ]⟩
  · exact ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-! ## Compute genericity (`WF`) per row -/

theorem cons_wf : ComputeTable.WF compInputs consPub where
  rlc5 h := by simp [consPub] at h
  size8 h := by simp [consPub] at h
  size11 _ := by
    constructor
    · show (consPub.sf1_e).size ≠ 0
      simp only [consPub, enc, GlobalCarryRecognizer.enc_size]
      show seedZ ^ leftResult.leaves ≠ 0
      exact pow_ne_zero _ seedZ_ne_zero
    · show (consPub.sf2_e).size ≠ 0
      simp only [consPub, enc, GlobalCarryRecognizer.enc_size]
      show seedZ ^ rightResult.leaves ≠ 0
      exact pow_ne_zero _ seedZ_ne_zero

theorem op1L_wf : ComputeTable.WF compInputs op1LPub where
  rlc5 h := by simp [op1LPub, op1PubOf] at h
  size8 h := by simp [op1LPub, op1PubOf] at h
  size11 h := by simp [op1LPub, op1PubOf] at h

theorem op1R_wf : ComputeTable.WF compInputs op1RPub where
  rlc5 h := by simp [op1RPub, op1PubOf] at h
  size8 h := by simp [op1RPub, op1PubOf] at h
  size11 h := by simp [op1RPub, op1PubOf] at h

/-! ## Whole-tree compute-row acceptance -/

theorem computeRowsAccepted : exec.ComputeRowsAccepted := by
  rw [ExactExecution.computeRowsAccepted_iff, computeRows_eq]
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl
  · exact ⟨rfl, rfl, cons_accepts⟩
  · exact ⟨rfl, rfl, op1L_accepts⟩
  · exact ⟨rfl, rfl, op1R_accepts⟩

/-! ## Arity-3 `Fcomp` topology on the branching compute tree -/

/-- The left `OP_1` child is a proper arity-3 `Fcomp` leaf. -/
theorem op1LRow_fcomp : ComputeTable.Fcomp op1LRow (fun _ => none) := by
  refine ⟨rfl, op1L_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [op1LRow, ComputeTable.fanoutComp]
  · intro i hi; simp [op1LRow, ComputeTable.fanoutComp] at hi

/-- The right `OP_1` child is a proper arity-3 `Fcomp` leaf. -/
theorem op1RRow_fcomp : ComputeTable.Fcomp op1RRow (fun _ => none) := by
  refine ⟨rfl, op1R_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [op1RRow, ComputeTable.fanoutComp]
  · intro i hi; simp [op1RRow, ComputeTable.fanoutComp] at hi

theorem op1LTree_rvt : RVT (ComputeTable.Fcomp (K := F)) (.node op1LRow []) := by
  unfold RVT
  refine ⟨?_, by simp, ?_⟩
  · rw [show (fun i : Fin 3 => (NTree.node op1LRow ([] : List (NTree _))).childLabel i)
        = (fun _ => none) by funext i; fin_cases i <;> rfl]
    exact op1LRow_fcomp
  · exact ⟨fun _ => op1LRow_fcomp, fun _ => rfl⟩

theorem op1RTree_rvt : RVT (ComputeTable.Fcomp (K := F)) (.node op1RRow []) := by
  unfold RVT
  refine ⟨?_, by simp, ?_⟩
  · rw [show (fun i : Fin 3 => (NTree.node op1RRow ([] : List (NTree _))).childLabel i)
        = (fun _ => none) by funext i; fin_cases i <;> rfl]
    exact op1RRow_fcomp
  · exact ⟨fun _ => op1RRow_fcomp, fun _ => rfl⟩

theorem computeTree_rvt : RVT (ComputeTable.Fcomp (K := F)) computeTree := by
  unfold computeTree RVT
  refine ⟨?_, ?_, ?_⟩
  · -- the `.cons` root links to its two `OP_1` children (fanout 2, `childLinkComp`)
    refine ⟨rfl, cons_accepts, ?_, ?_⟩
    · intro i
      fin_cases i <;>
        simp [consRow, ComputeTable.fanoutComp, NTree.childLabel, NTree.childOpt]
    · intro i hi
      fin_cases i
      · simp [consRow, op1LRow, op1LPub, op1PubOf, consPub, ComputeTable.sfTriple,
          NTree.childLabel, NTree.childOpt, NTree.label]
      · simp [consRow, op1RRow, op1RPub, op1PubOf, consPub, ComputeTable.sfTriple,
          NTree.childLabel, NTree.childOpt, NTree.label]
      · simp [consRow, ComputeTable.fanoutComp] at hi
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact op1LTree_rvt
    · exact op1RTree_rvt
  · refine ⟨fun h => absurd h (by simp [NTree.isLeaf]), fun h => ?_⟩
    exfalso
    have h0 := h.2.2.1 ⟨0, by norm_num⟩
    simp [ComputeTable.fanoutComp, consRow] at h0

theorem compute_topology : ComputeExactTopology exec := by
  refine ⟨?_, ?_⟩
  · show RVT (ComputeTable.Fcomp (K := F)) exec.computeTree
    exact computeTree_rvt
  · show ProperArity 3 exec.computeTree
    simp [exec, computeTree]

end

end Nock.NockVMROM.Thm54.TraceGen.ConsConfig

#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.cons_accepts
#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.computeRowsAccepted
#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.compute_topology
