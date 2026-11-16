/-
  Nock/RedTeam/Batch715Thm54MoveMDecision.lean

  * The reflected memory AIR's `intermediate`
    gates read the paper's nine-slot pole: `memInterExprs_read_root_sound` is literally
    `pole minp mrow.mem mrow.cprime * mg = 1 ∧ …` (cited; `Reified.poleExpr = recRLCExpr − chl 1`).  Any
    relation that instead demands `(pole + t)·g = 1` agrees with it only when `t = 0`
    (`ten_slot_disagrees`): with `t = γ⁹·exp`, exactly the rows with `γ ≠ 0 ∧ exp ≠ 0` — every honest
    record row at every honest coin with `γ ≠ 0`.  So a ten-slot `interR` in `MemoryTable` with a
    nine-slot reflected AIR makes `memoryAIR_sound` and hence `exactChainedHasCanonicalRAP2.memory_iff`
    false.
  * **Q4 — the cheap check that catches it (rule 4g).**  Proof-term reach: from the frontier theorem
    `exactChainedHasCanonicalRAP2` (whose fingerprint is its TYPE) the proof reaches `MemoryTable.pole`,
    `recRLC`, `interR`, `Trans.memoryAIRchained`, `Reified.poleExpr` (`frontier_proof_reaches`) — seconds,
    no build.
  * **Q2 — the binding does not read the accumulators.**  `BindMemoryRow` is invariant under the row's
    `ipre`/`icur` and the inputs' `β` (`bindMemoryRow_beta_free`): the paper's `interV` plays no part in
    binding, so a β-free topology predicate suffices for `hc`/`hm` and for the topology receipts — no
    mirror change is needed to remove `hexp0`.
  * **Q3 — ten-slot LIO implies nine-slot LIO** on the prefixes when the truncated responses stay nodup
    (`lio_trunc9`): the strategy-level `ioStrategy K 9` (the paper's object) is reachable from the chip's
    ten-slot LIO by truncation; the mirror need not grow for Part 2 either.
-/
import Lean
import Nock.AIR
import Nock.NockVMROM.Thm54.SemanticStrategy
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.MemoryInternalPole
import Nock.NockVMROM.Thm54.FamilyMemoryRows
import Nock.NockVMROM.Thm54.ExactCanonicalRAP
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Lean Elab Command

namespace Nock.RedTeam.Batch715

open Nock Nock.MemoryTable Nock.NockVMROM.Thm54

/-! ## Q1 -/

section Mechanism
variable {K : Type} [Field K]

/-- A nine-slot inverse gate and a ten-slot one agree on a row only when the tenth term vanishes. -/
theorem ten_slot_disagrees (p t g : K) (h9 : p * g = 1) (h10 : (p + t) * g = 1) : t = 0 := by
  have hg : g ≠ 0 := by rintro rfl; simp at h9
  have : t * g = 0 := by linear_combination h10 - h9
  exact (mul_eq_zero.mp this).resolve_right hg

/-- The tenth term `γ⁹·e` is nonzero exactly off `γ = 0 ∨ e = 0`. -/
theorem tenth_term_ne (g e : K) (hg : g ≠ 0) (he : e ≠ 0) : g ^ 9 * e ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ hg) he

end Mechanism

/-! ## Q2 — binding ignores β and the accumulators -/

section BetaFree
variable {K : Type} [Field K]

theorem bindMemoryRow_beta_free (z : K) (s : SemanticStrategy.MemoryRowSkeleton)
    (st : MState) (inp : Inputs K) (pub : Pub K) (β' ipre' icur' : K) :
    SemanticStrategy.BindMemoryRow z s (st, (inp, pub)) ↔
      SemanticStrategy.BindMemoryRow z s
        (st, ({ inp with β := β' }, { pub with ipre := ipre', icur := icur' })) := by
  exact Iff.rfl

end BetaFree

/-! ## Q3 — LIO on ten slots gives LIO on the nine-slot prefixes -/

section Trunc
variable {K : Type} [DecidableEq K]

def trunc9 (v : Fin 10 → K) : Fin 9 → K := fun d => v d.castSucc

theorem lio_trunc9 (Ksz : ℕ) (req resp : List (Fin 10 → K))
    (h : IO.LIO Ksz req resp) (hnd : (resp.map trunc9).Nodup) :
    IO.LIO Ksz (req.map trunc9) (resp.map trunc9) := by
  obtain ⟨hrange, -, hperm⟩ := h
  refine ⟨by simpa using hrange, hnd, hperm.map _⟩

end Trunc

/-! ## Q4 / Q2 — proof-term reach -/

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

def mirrorNames : Array Name := #[``Nock.MemoryTable.pole, ``Nock.MemoryTable.recRLC,
  ``Nock.MemoryTable.interR, ``Nock.MemoryTable.interV, ``Nock.MemoryTable.Vmem,
  ``Nock.MemoryTable.Fmem, ``Nock.Reified.poleExpr, ``Nock.Reified.Trans.memoryAIRchained]

run_cmd do
  let env ← getEnv
  -- the frontier theorem's PROOF reaches the mirror's pole and the reflected AIR
  let cl := reach env #[``Nock.NockVMROM.Thm54.exactChainedHasCanonicalRAP2]
  let hits := mirrorNames.filter cl.contains
  logInfo m!"frontier_proof_reaches: exactChainedHasCanonicalRAP2 → {hits}"
  for n in [``Nock.MemoryTable.pole, ``Nock.MemoryTable.recRLC, ``Nock.MemoryTable.interR,
      ``Nock.Reified.poleExpr, ``Nock.Reified.Trans.memoryAIRchained] do
    unless cl.contains n do throwError m!"expected {n} in the proof reach"
  let roots := #[``Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.optimizedFullStrict_hostile_LIO_historical,
    ``Nock.NockVMROM.Thm54.MemoryInternalPole.optimizedFullStrict_paired_records,
    ``Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.hostile_timestamp_eq,
    ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.memoryForestAlphaEventOf_card_le,
    ``Nock.NockVMROM.Thm54.FormRAxisEvent.formRLambdaEvent_card_le]
  let cl2 := reach env roots
  let forbidden := #[``Nock.MemoryTable.interV, ``Nock.MemoryTable.Vmem, ``Nock.MemoryTable.Fmem,
    ``Nock.MemoryTable.pole, ``Nock.MemoryTable.interR,
    ``Nock.NockVMROM.Thm54.FamilyMemoryRows.deployed_row_vmem_at]
  let bad := forbidden.filter cl2.contains
  unless bad.isEmpty do throwError m!"R4 route reaches the mirror: {bad}"
  logInfo m!"r4_route_avoids_mirror: {cl2.size} constants; none of interV/Vmem/Fmem/pole/interR/deployed_row_vmem_at"

end Nock.RedTeam.Batch715
