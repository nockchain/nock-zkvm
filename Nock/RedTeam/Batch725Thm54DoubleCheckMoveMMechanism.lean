/-
  Nock/RedTeam/Batch725Thm54DoubleCheckMoveMMechanism.lean

  * `memoryEnvFull_no_exponent_column` / `memoryAIR_numTraceCols`: the
    reflected memory env has 36 columns, `0..35`; `tc 35` is `cprime`, and every index `≥ 36` reads
    `0` — there is no exponent-carrying column for a route (d).  CONFIRMED.
  * **Check 2 (the architectural premise).**  The report says the mirror and the reflected AIR
    "stay faithful to `:2090-2171`" and that the deviation "belongs on the chip side, documented".
    So the
    premise "the paper layer is faithful and deviations are not propagated" is contradicted by the
    tree's own precedent; what is true is that growing the mirror to ten slots forces growing the
    reflected AIR too (route (b)), which is the cost the report declines.  Recorded as a correction
    to the report's reasoning, not to its verdict.
  * **Check 5 (R4 avoids the mirror).**
-/
import Lean
import Nock.AIR
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.MemoryInternalPole
import Nock.NockVMROM.Thm54.FamilyMemoryRows
import Nock.NockVMROM.Thm54.ExactCanonicalRAP
import Nock.RedTeam.Batch672Thm54ExponentCarrierBinding
import Nock.RedTeam.Batch501Thm54MemoryTopology
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Lean Elab Command

namespace Nock.RedTeam.Batch725

open Nock Nock.MemoryTable Nock.NockVMROM.Thm54


section Mechanism
variable {K : Type} [Field K]

theorem ten_slot_disagrees' (p t g : K) (h9 : p * g = 1) (h10 : (p + t) * g = 1) : t = 0 := by
  have htg : t * g = 0 := by
    calc t * g = (p + t) * g - p * g := by ring
      _ = 0 := by rw [h9, h10, sub_self]
  rcases mul_eq_zero.mp htg with ht | hg
  · exact ht
  · exfalso
    rw [hg, mul_zero] at h9
    exact zero_ne_one h9

/-- **On the reflected AIR itself.**  If the paper's nine-slot `read_root` inverse gates vanish on a
row (`memInterExprs_read_root_sound`: `pole · g = 1 ∧ icur − ipre = g`), then NO ten-slot inverse
relation `(pole + t) · g = 1` with `t ≠ 0` holds on that row. -/
theorem reflected_read_root_rejects_tenth_term
    (minp : MemoryTable.Inputs K) (mop : MState → K) (mrow : MemoryTable.Pub K) (mg t : K)
    (hgates : ∀ e ∈ Reified.memInterExprs MState.read_root,
      e.eval (Reified.memoryEnvFull minp mop mrow mg) = 0)
    (ht : t ≠ 0) :
    ¬ (pole minp mrow.mem mrow.cprime + t) * mg = 1 := by
  intro h10
  have h9 := ((Reified.memInterExprs_read_root_sound minp mop mrow mg).mp hgates).1
  exact ht (ten_slot_disagrees' _ _ _ h9 h10)

/-- Same for `verify_child`. -/
theorem reflected_verify_child_rejects_tenth_term
    (minp : MemoryTable.Inputs K) (mop : MState → K) (mrow : MemoryTable.Pub K) (mg t : K)
    (hgates : ∀ e ∈ Reified.memInterExprs MState.verify_child,
      e.eval (Reified.memoryEnvFull minp mop mrow mg) = 0)
    (ht : t ≠ 0) :
    ¬ (pole minp mrow.mem mrow.cprime + t) * mg = 1 := by
  intro h10
  have h9 := ((Reified.memInterExprs_verify_child_sound minp mop mrow mg).mp hgates).1
  exact ht (ten_slot_disagrees' _ _ _ h9 h10)

theorem tenth_term_ne' (g e : K) (hg : g ≠ 0) (he : e ≠ 0) : g ^ 9 * e ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ hg) he

/-- **No route (d): the reflected memory env has no exponent column.**  Columns `0..35` are the
paper's labels, record, accumulator pair, the free inverse witness, `z⁻¹` and Form R's `C'`; every
index from `36` on reads `0`. -/
theorem memoryEnvFull_no_exponent_column
    (minp : MemoryTable.Inputs K) (mop : MState → K) (mrow : MemoryTable.Pub K) (mg : K)
    (i : ℕ) (hi : 36 ≤ i) :
    (Reified.memoryEnvFull minp mop mrow mg).trace i = 0 := by
  simp only [Reified.memoryEnvFull]
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> first | omega | rfl

/-- The reflected memory AIR declares 36 trace columns and 9 challenge columns. -/
theorem memoryAIR_numTraceCols : (Reified.memoryAIR (K := K)).numTraceCols = 36 := rfl
theorem memoryAIR_numChallenges : (Reified.memoryAIR (K := K)).numChallenges = 9 := rfl

end Mechanism


section AlreadyDeviated
variable {K : Type} [Field K]

theorem recRLC_ninth_slot (γ : K) (r : ComputeTable.MemRec K) (c : K) :
    recRLC γ r c =
      (r.root.size + γ * r.root.dyck + γ ^ 2 * r.root.leaf
        + γ ^ 3 * r.child.size + γ ^ 4 * r.child.dyck + γ ^ 5 * r.child.leaf
        + γ ^ 6 * r.axis + γ ^ 7 * r.ts) + γ ^ 8 * c := rfl

/-- The reflected AIR reads `C'` at trace column 35 … -/
theorem memoryEnvFull_col35_cprime
    (minp : MemoryTable.Inputs K) (mop : MState → K) (mrow : MemoryTable.Pub K) (mg : K) :
    (Reified.memoryEnvFull minp mop mrow mg).trace 35 = mrow.cprime := rfl

/-- … and the Form R coin `λ` at challenge column 8 (the paper's `:2123` has `β`, `γ` only). -/
theorem memoryEnvFull_chal8_lambda
    (minp : MemoryTable.Inputs K) (mop : MState → K) (mrow : MemoryTable.Pub K) (mg : K) :
    (Reified.memoryEnvFull minp mop mrow mg).chal 8 = mrow.lambda := rfl

/-- The reflected pole is the NINE-slot `recRLCExpr − β`, with `tc 35` (= `C'`) at `γ⁸`
(`poleExpr_eval` is the production receipt; restated here as the value identity). -/
theorem poleExpr_is_nine_slot
    (minp : MemoryTable.Inputs K) (mop : MState → K) (mrow : MemoryTable.Pub K) (mg : K) :
    Reified.poleExpr.eval (Reified.memoryEnvFull minp mop mrow mg) =
      recRLC minp.γ mrow.mem mrow.cprime - minp.β :=
  Reified.poleExpr_eval minp mop mrow mg

end AlreadyDeviated

/-! ## Check 5 — proof-term reach, re-run and extended -/

partial def reach (env : Environment) (roots : Array Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut work := roots.toList
  while true do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      if !(`Nock).isPrefixOf n then continue
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
        for c in cs do
          unless seen.contains c do work := c :: work
  return seen

def moveMNames : Array Name := #[``Nock.MemoryTable.Vmem, ``Nock.MemoryTable.interV,
  ``Nock.MemoryTable.pole, ``Nock.MemoryTable.recRLC, ``Nock.MemoryTable.eqBlk,
  ``Nock.MemoryTable.Pub, ``Nock.MemoryTable.Inputs, ``Nock.ComputeTable.MemRec]

def mirrorNames : Array Name := #[``Nock.MemoryTable.Fmem, ``Nock.MemoryTable.interR,
  ``Nock.NockVMROM.Thm54.FamilyMemoryRows.deployed_row_vmem_at,
  ``Nock.NockVMROM.Thm54.FamilyMemoryRows.expShiftInputs,
  ``Nock.RedTeam.Batch501.hFcommit_memory_of_good,
  ``Nock.RedTeam.Batch501.deployed_forestReconGoal,
  ``Nock.RedTeam.Batch490.hFcommit_memory]

def carrierNames : Array Name := #[``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.reqIdxRLCTerm,
  ``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.recordRLC,
  ``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.reqIdxCol,
  ``Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator.hostileRequests]

def report (env : Environment) (tag : String) (roots : Array Name) : CommandElabM Unit := do
  for r in roots do
    unless (env.find? r).isSome do throwError m!"missing root {r}"
  let cl := reach env roots
  let hitM := moveMNames.filter cl.contains
  let hitMirror := mirrorNames.filter cl.contains
  let hitCarrier := carrierNames.filter cl.contains
  logInfo m!"{tag}: {cl.size} constants\n  MoveM names reached: {hitM}\n  mirror/transfer names reached: {hitMirror}\n  carrier controls reached: {hitCarrier}"

run_cmd do
  let env ← getEnv
  let r715 := #[``Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.optimizedFullStrict_hostile_LIO_historical,
    ``Nock.NockVMROM.Thm54.MemoryInternalPole.optimizedFullStrict_paired_records,
    ``Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.hostile_timestamp_eq,
    ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.memoryForestAlphaEventOf_card_le,
    ``Nock.NockVMROM.Thm54.FormRAxisEvent.formRLambdaEvent_card_le]
  report env "A. Batch715 roots" r715
  let clA := reach env r715
  -- None of interV/Vmem/Fmem/pole/interR/deployed_row_vmem_at
  for n in [``Nock.MemoryTable.interV, ``Nock.MemoryTable.Vmem, ``Nock.MemoryTable.Fmem,
      ``Nock.MemoryTable.pole, ``Nock.MemoryTable.interR,
      ``Nock.NockVMROM.Thm54.FamilyMemoryRows.deployed_row_vmem_at] do
    if clA.contains n then throwError m!"Batch715 claim fails to reproduce: {n} reached"
  -- positive control: the instrument sees the carrier names from the same roots
  for n in carrierNames do
    unless clA.contains n do throwError m!"positive control failed: {n} not reached from A"
  report env "B. Batch672 binding roots" #[``Nock.RedTeam.Batch672.ts_eq_alpha_pow_natLift,
    ``Nock.RedTeam.Batch672.natLift_reqIdx_window, ``Nock.RedTeam.Batch672.memory_row_bound]
  -- (c) R4's other named ingredients
  report env "C. nodup / ln0" #[``Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.hostile_requests_nodup,
    ``Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.hostile_ln0_eq_one]
  -- (d) the walk reconstruction the corrected §32 names (BFS inversion of `fo`)
  report env "D. walk reconstruction (Batch501.deployed_forestVecBFT_pt)"
    #[``Nock.RedTeam.Batch501.deployed_forestVecBFT_pt]
  -- (e) the per-row equality transfer an accumulator telescoping would use
  report env "E. eqBlk transfer (FamilyMemoryRows.eqBlk_of_paper_classes)"
    #[``Nock.NockVMROM.Thm54.FamilyMemoryRows.eqBlk_of_paper_classes]
  let clF := reach env #[``Nock.NockVMROM.Thm54.exactChainedHasCanonicalRAP2]
  for n in [``Nock.MemoryTable.pole, ``Nock.MemoryTable.recRLC, ``Nock.MemoryTable.interR,
      ``Nock.Reified.poleExpr, ``Nock.Reified.Trans.memoryAIRchained] do
    unless clF.contains n do throwError m!"frontier control failed: {n}"
  logInfo m!"F. exactChainedHasCanonicalRAP2 reaches pole/recRLC/interR/poleExpr/memoryAIRchained (replicated)"

end Nock.RedTeam.Batch725
