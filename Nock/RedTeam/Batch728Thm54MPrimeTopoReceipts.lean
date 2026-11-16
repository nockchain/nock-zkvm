/-
  Nock/RedTeam/Batch728Thm54MPrimeTopoReceipts.lean

  Lane; notes only, no `passed` flip.

  * **R1 — honest non-vacuity** (`fmemTopo_at_honest_tuple`, the shape of
    `Batch726.fmemTopo_at_honest_tuple`, now through the PRODUCTION predicate and the restated
    `Batch490.hFcommit_memory`): at the honest tuple the family chip is the package chip
    (`memoryChipAt_honest_of_chalVal`), so the package's own `memory_satisfies` gives `FmemTopo`
    at every row.  Two forms: from `OptimizedProductionAcceptanceAt … P.honestTuple`
    (`fmemTopo_at_honest_acceptance`, the field `memory_satisfies` itself) and from the canonical
    memory trace (`fmemTopo_at_canonical_trace`, `canonicalMemoryTrace_satisfies`).  No hypothesis
    mentions `γ`, `β`, `reqIdx`, `rowExpTerm` or the pole (checked by R4's `run_cmd`).  Contrast:
    the withdrawn `hexp0 : ∀ i, rowExpTerm = 0` is false at every honest record row with `γ ≠ 0`
    (`Batch679.rowExpTerm_eq_zero_iff`), so the old statements were vacuous there.
  * **R2 — the restatement is not a weakening of any consumer's input**
    (`rvtWithArity_topo_of_fmem`, `memoryTopo_of_exactTopology`): the production
    `MemoryExactTopology exec` implies the β-free `∀ t ∈ exec.memoryForest, RVTWithArity FmemTopo t`,
    so every re-typed consumer  accepts every input it accepted before.
  * **R3 — `Batch448` stays on `trunc9`** (`batch448_trunc9_lio`): the chip's ten-slot `IO.LIO`
    gives the nine-slot LIO on the `Batch448.trunc9` prefixes given nodup of the truncated responses
    (`Batch715.lio_trunc9`; `hnd` is a named cell of Part 2's census).
-/
import Lean
import Nock.NockVMROM.Thm54.MemoryTopoBetaFree
import Nock.NockVMROM.Thm54.OptimizedCanonicalTraces
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch490Thm54TopologyAssembly
import Nock.RedTeam.Batch501Thm54MemoryTopology
import Nock.RedTeam.Batch509Thm54WrapSpecialize
import Nock.RedTeam.Batch524Thm54DecodeMemoryRowIn
import Nock.RedTeam.Batch715Thm54MoveMDecision
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch728

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.MemoryTable Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MemoryTopoBetaFree
open Nock.NockVMROM.Thm54.FamilyMemoryRows (MemStateTagChar)
open Nock.NockVMROM.Thm54.OptimizedStrictPackage Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.Framework Nock.Framework.Reify MonolithicRAP

/-! ## R1 — non-vacuity on an honest trace -/

section Honest

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Transport of the package chip's acceptance to the family chip when the two chips coincide
(the dependent `Fin.cast` is the identity once `C = P.memoryChip`; `Batch726`'s lemma). -/
theorem satisfies_familyQm_of_chip_eq
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (hEq : P.memoryChipAt c = P.memoryChip)
    (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm) :
    RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (WrapMemoryConjuncts.familyQm P c Qm) := by
  have key : ∀ (C : _) (h : C = P.memoryChip) (hw : C.rap.w = P.memoryChip.rap.w),
      RAP.SatisfiesWithPreprocessing C (fun j => Qm (Fin.cast hw j)) := by
    intro C h hw
    subst h
    simpa using hsat
  exact key _ hEq (FamilyComputeRows.memoryChipAt_width P c)

/-- **R1 (M′ non-vacuity receipt).**  At the honest tuple, every row of a trace the PACKAGE chip
accepts satisfies the production `FmemTopo`.  Hypotheses: the `chalVal` pin
(`memoryChipAt_honest_of_chalVal`'s premise), the package chip's acceptance, `MemStateTagChar`,
`z ≠ 0` — no `hexp0`, no `hpole`, no condition on `γ` or `reqIdx`. -/
theorem fmemTopo_at_honest_tuple
    (h : DeployedChipFamily.memoryChalValOfTuple P.optimized.basis P.honestTuple =
      P.optimized.memoryChallenge)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
    (hchar : MemStateTagChar F)
    (hz : nprSeed P.honestTuple.1 ≠ 0)
    (i : ℕ) (hi1 : 1 ≤ i)
    (hih : i ≤ P.optimized.family.problem.cfg.memRows) :
    FmemTopo (ExecOfTraces.lblM P Qm P.honestTuple i)
      (fun j : Fin 2 =>
        if (j : ℕ) < ExecOfTraces.foM P Qm P.honestTuple i then
          some (Batch490.clabOfMem (ExecOfTraces.lblM P Qm P.honestTuple) i ((j : ℕ) + 1))
        else none) :=
  Batch490.hFcommit_memory P P.honestTuple Qm
    (satisfies_familyQm_of_chip_eq P P.honestTuple Qm (P.memoryChipAt_honest_of_chalVal h) hsat)
    hchar hz i hi1 hih

/-- Its
package-chip `memory_satisfies` field. -/
theorem fmemTopo_at_honest_acceptance
    (h : DeployedChipFamily.memoryChalValOfTuple P.optimized.basis P.honestTuple =
      P.optimized.memoryChallenge)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm P.honestTuple)
    (hchar : MemStateTagChar F)
    (hz : nprSeed P.honestTuple.1 ≠ 0)
    (i : ℕ) (hi1 : 1 ≤ i)
    (hih : i ≤ P.optimized.family.problem.cfg.memRows) :
    FmemTopo (ExecOfTraces.lblM P Qm P.honestTuple i)
      (fun j : Fin 2 =>
        if (j : ℕ) < ExecOfTraces.foM P Qm P.honestTuple i then
          some (Batch490.clabOfMem (ExecOfTraces.lblM P Qm P.honestTuple) i ((j : ℕ) + 1))
        else none) :=
  fmemTopo_at_honest_tuple P h Qm hacc.memory_satisfies hchar hz i hi1 hih

/-- R1, on the package's own canonical memory trace (`canonicalMemoryTrace_satisfies`): the honest
trace, at the honest tuple. -/
theorem fmemTopo_at_canonical_trace
    (h : DeployedChipFamily.memoryChalValOfTuple P.optimized.basis P.honestTuple =
      P.optimized.memoryChallenge)
    (hmore : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < P.optimized.family.problem.cfg.kMem →
        (P.optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hC : P.optimized.family.problem.exec.CprimeCoherent)
    (hchar : MemStateTagChar F)
    (hz : nprSeed P.honestTuple.1 ≠ 0)
    (i : ℕ) (hi1 : 1 ≤ i)
    (hih : i ≤ P.optimized.family.problem.cfg.memRows) :
    FmemTopo (ExecOfTraces.lblM P (MultiRootOptimizedAcceptance.canonicalMemoryTrace P)
        P.honestTuple i)
      (fun j : Fin 2 =>
        if (j : ℕ) < ExecOfTraces.foM P (MultiRootOptimizedAcceptance.canonicalMemoryTrace P)
            P.honestTuple i then
          some (Batch490.clabOfMem (ExecOfTraces.lblM P
            (MultiRootOptimizedAcceptance.canonicalMemoryTrace P) P.honestTuple) i ((j : ℕ) + 1))
        else none) :=
  fmemTopo_at_honest_tuple P h _
    (MultiRootOptimizedAcceptance.canonicalMemoryTrace_satisfies P hmore hC) hchar hz i hi1 hih

end Honest

/-! ## R2 — the production topology implies the β-free one (no consumer input is lost) -/

section NotWeaker
variable {K : Type} [Field K]

/-- `RVTWithArity Fmem t → RVTWithArity FmemTopo t`.  Node-wise `fmemTopo_of_fmem`; the leaf clause
transfers because `FmemTopo l ⊥` forces `fanout = 0`, and `Fmem`'s dynamic clause at the real
children then forces no child. -/
theorem rvtWithArity_topo_of_fmem {t : NTree (MState × DTmem K)}
    (h : RVTWithArity (Fmem (K := K)) t) : RVTWithArity (FmemTopo (K := K)) t := by
  refine ⟨?_, h.arity⟩
  have hr := (RVT_iff_forall_InTree (Fmem (K := K)) t).mp h.rvt
  refine (RVT_iff_forall_InTree (FmemTopo (K := K)) t).mpr ?_
  intro s hs
  obtain ⟨hF, hleaf⟩ := hr s hs
  refine ⟨fmemTopo_of_fmem _ _ hF, ?_⟩
  constructor
  · intro hl
    exact fmemTopo_of_fmem _ _ (hleaf.mp hl)
  · intro hT
    have h0 := (hT.2.2.1 ⟨0, by norm_num⟩)
    simp only [ne_eq, not_true_eq_false, iff_false, not_lt, Nat.le_zero] at h0
    have hc := (hF.2.2.1 ⟨0, by norm_num⟩)
    rw [h0] at hc
    simp only [Nat.lt_irrefl, false_iff, not_not] at hc
    cases s with
    | node l ch =>
      simp only [NTree.childLabel, NTree.childOpt, NTree.children_node, Option.map_eq_none_iff] at hc
      cases ch with
      | nil => rfl
      | cons _ _ => simp at hc

/-- The production `MemoryExactTopology` implies the β-free whole-forest topology: every input the
re-typed consumers  took before still feeds them. -/
theorem memoryTopo_of_exactTopology {F : Type} [Field F] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : MemoryExactTopology exec) :
    ∀ t ∈ exec.memoryForest, RVTWithArity (FmemTopo (K := K)) t :=
  fun t ht => rvtWithArity_topo_of_fmem (h t ht)

end NotWeaker


section Trunc
variable {K : Type} [DecidableEq K]

theorem batch448_trunc9_eq : (Batch448.trunc9 : (Fin 10 → K) → Fin 9 → K) = Batch715.trunc9 :=
  rfl

/-- **R3.**  The chip-level ten-slot `IO.LIO` gives the strategy-level nine-slot `IO.LIO` on
`Batch448.trunc9` prefixes, given nodup of the truncated responses (`Batch715.lio_trunc9`). -/
theorem batch448_trunc9_lio (Ksz : ℕ) (req resp : List (Fin 10 → K))
    (h : IO.LIO Ksz req resp) (hnd : (resp.map Batch448.trunc9).Nodup) :
    IO.LIO Ksz (req.map Batch448.trunc9) (resp.map Batch448.trunc9) :=
  Batch715.lio_trunc9 Ksz req resp h hnd

end Trunc

end Nock.RedTeam.Batch728


open Lean Elab Command

namespace Nock.RedTeam.Batch728

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

/-- The restated theorems (M′). -/
def restated : Array Name := #[
  ``Nock.RedTeam.Batch490.deployed_lblM_eqBlk,
  ``Nock.RedTeam.Batch490.hFcommit_memory,
  ``Nock.RedTeam.Batch501.hFcommit_memory_of_good,
  ``Nock.RedTeam.Batch501.deployed_forestReconGoal,
  ``Nock.RedTeam.Batch501.execOfTraces_memoryTopology,
  ``Nock.RedTeam.Batch501.memoryTopology_of_deployed,
  ``Nock.RedTeam.Batch501.memoryTopology_of_deployed_of_good,
  ``Nock.RedTeam.Batch509.fmem_of_topology,
  ``Nock.RedTeam.Batch509.wrap_idA_lblM_of_topology,
  ``Nock.RedTeam.Batch509.specialized_memoryForest_eq,
  ``Nock.RedTeam.Batch509.wrapSpecializeJoin,
  ``Nock.RedTeam.Batch509.specializedMemoryTopology_of_exec,
  ``Nock.RedTeam.Batch524.memoryTreeBinds_of_topology',
  ``Nock.RedTeam.Batch728.fmemTopo_at_honest_tuple,
  ``Nock.RedTeam.Batch728.fmemTopo_at_honest_acceptance,
  ``Nock.RedTeam.Batch728.fmemTopo_at_canonical_trace]

/-- Substrings no restated TYPE may mention (β / accumulator / exponent / pole). -/
def forbiddenSubs : List String :=
  ["Vmem", "interV", "rowExpTerm", "poleSource", "reqIdx", "expShift"]

/-- Exact names no restated TYPE may mention (the production topology objects). -/
def forbiddenExact : List Name :=
  [``Nock.MemoryTable.Fmem, ``Nock.NockVMROM.Thm54.MemoryExactTopology,
    ``Nock.RedTeam.Batch502.specializedMemoryTopology]

def mentions (env : Environment) (n : Name) (sub : String) : Bool := Id.run do
  let some ci := env.find? n | return false
  return ci.type.getUsedConstants.any fun c => (c.toString.splitOn sub).length > 1

def mentionsExact (env : Environment) (n m : Name) : Bool := Id.run do
  let some ci := env.find? n | return false
  return ci.type.getUsedConstants.contains m

run_cmd do
  let env ← getEnv
  for n in restated do
    unless (env.find? n).isSome do throwError m!"missing {n}"
    for sub in forbiddenSubs do
      if mentions env n sub then throwError m!"{n}'s type mentions {sub}"
    for m in forbiddenExact do
      if mentionsExact env n m then throwError m!"{n}'s type mentions {m}"
    -- every restated statement is about the β-free predicate (positive control on the instrument)
    let ci := (env.find? n).get!
    let cs := ci.type.getUsedConstants
    let topoNames := [``Nock.NockVMROM.Thm54.MemoryTopoBetaFree.FmemTopo,
      ``Nock.MemoryTable.eqBlk, ``Nock.RedTeam.Batch509.specializedMemoryTopologyTopo,
      ``Nock.RedTeam.Batch524.MemoryTreeBindsA]
    unless cs.any (topoNames.contains ·) do throwError m!"{n}'s type names no β-free object"
  -- positive control: the instrument sees the pole in a statement that really carries it
  unless mentions env ``Nock.RedTeam.Batch501.hpole_of_good "poleSource" do
    throwError "positive control failed: hpole_of_good"
  unless mentionsExact env ``Nock.RedTeam.Batch502.exec_memoryTopology_is_not_specialized
      ``Nock.NockVMROM.Thm54.MemoryExactTopology do
    throwError "positive control failed: Batch502 exact-topology statement"
  logInfo m!"B728 R4: {restated.size} restated statements mention no Vmem/interV/Fmem/MemoryExactTopology/rowExpTerm/pole/reqIdx; positive control hpole_of_good"

run_cmd do
  let env ← getEnv
  let newNames : Array Name := restated ++ #[
    ``Nock.NockVMROM.Thm54.MemoryTopoBetaFree.FmemTopo,
    ``Nock.NockVMROM.Thm54.MemoryTopoBetaFree.mem_stateSep_topo,
    ``Nock.NockVMROM.Thm54.MemoryTopoBetaFree.respects_pt_topo,
    ``Nock.NockVMROM.Thm54.MemoryTopoBetaFree.memoryFingerprintStructure_of_rvtWithArity_topo,
    ``Nock.RedTeam.Batch509.specializedMemoryTopologyTopo]
  for cap in [``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod,
      ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package] do
    unless (env.find? cap).isSome do throwError m!"missing capstone {cap}"
    let cl := reach env #[cap]
    let hits := newNames.filter cl.contains
    logInfo m!"B728 R5 (36th): {cap} reaches M′ names {hits}"
    unless cl.contains ``Nock.MemoryTable.Fmem do throwError m!"positive control failed at {cap}"
    logInfo m!"B728 R5: {cap} ({cl.size} constants) reaches none of the {newNames.size} M′ names; reaches MemoryTable.Fmem (control)"

end Nock.RedTeam.Batch728

#print axioms Nock.RedTeam.Batch728.fmemTopo_at_honest_tuple
#print axioms Nock.RedTeam.Batch728.fmemTopo_at_honest_acceptance
#print axioms Nock.RedTeam.Batch728.fmemTopo_at_canonical_trace
#print axioms Nock.RedTeam.Batch728.rvtWithArity_topo_of_fmem
#print axioms Nock.RedTeam.Batch728.memoryTopo_of_exactTopology
#print axioms Nock.RedTeam.Batch728.batch448_trunc9_lio
