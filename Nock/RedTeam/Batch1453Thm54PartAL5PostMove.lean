import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesHostile
import Nock.NockVMROM.Thm54.HostileSemanticSoundness
import Nock.RedTeam.Batch1351Thm54CompletenessCut
import Nock.RedTeam.Batch366Thm54ForeignCoinRejection
import Nock.RedTeam.Batch1420Thm54PartAL3Honest12
import Nock.RedTeam.Batch1431Thm54PartAStaged
import Nock.RedTeam.Batch1450Thm54PartAWalkCompleteness
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1453Thm54PartAL5PostMove.lean

  * **(C4) reached, not used, for the new soundness roots.**  `Batch1351`'s instrument re-run at the
    roots the statement now consumes (`acceptance_outside_failure_implies_target309`,
    `optimizedFalseAcceptance309_probability_le`, `stagedFalseAcceptance309_probability_le`,
    `HostileSemanticSoundness.hostileSemanticSoundness_pinned`): every use of the realization
    structures (`OptimizedComputeRealizationAt` and the 309 twin) in the reach set is one of
    `nodes_injective` / `adjacent_orbit` / `mk` / the two projections, so the honest-completeness
    field `canonical_satisfies` (whose proof argument contains `witness10_accepts`) is reached and
    never projected; the generator's canonical 309 trace, `canonical_satisfies309` and
    `genBuildableOfProgram` are not reached.  Positive control: `Batch1431.gen_honest_accepted309`
    reaches all of them.
  * **Honest rejection at a foreign twelve-coin tuple** (`parallel_rejected_at_foreign_pole`,
    `honest_rejected_at_foreign_pole12`): if a memory trace is accepted by the twelve-coin memory chip
    at `c`, no compute trace is accepted with it at `c` with the IO pole moved by one
    (through `memSat_at_view` and `Batch366.foreign_ioPole_rejects_succ` at the memory view).
    A non-vacuity check (the
    parallel chips read `c`), not a soundness premise.  The width-abstracted `castFin_gen` keeps the
    kernel from comparing the two chips' widths (the earlier `Fin.ext rfl` cast timed out).
  * `#print axioms` of the four headline results and the figures at the swapped objects.

  Nothing here states or implies `:966` soundness at `deployedChronology`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1453

open scoped Polynomial
open Polynomial
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.PartA12

noncomputable section

section Foreign

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- A twelve-coin tuple with its IO pole (`c.2.1.2`) replaced. -/
def withIoPole12 (c : OptimizedProductionChallengeTuple12 K F) (pole : K) :
    OptimizedProductionChallengeTuple12 K F :=
  (c.1, ((c.2.1.1, pole), c.2.2))

theorem walkView11_withIoPole12 (c : OptimizedProductionChallengeTuple12 K F) (pole : K) :
    walkView11 (withIoPole12 c pole) = Batch366.withIoPole (walkView11 c) pole := rfl

theorem withIoPole12_ne (c : OptimizedProductionChallengeTuple12 K F) :
    withIoPole12 c (c.2.1.2 + 1) ≠ c := by
  intro h
  have h2 := congrArg (fun c : OptimizedProductionChallengeTuple12 K F => c.2.1.2) h
  simp only [withIoPole12] at h2
  exact one_ne_zero (add_left_cancel (h2.trans (add_zero _).symm))

/-- Width-abstracted reindexing: the kernel never compares two chips' widths. -/
theorem castFin_gen {X : Type} {n m k : ℕ} (Q : Fin k → X) (h1 : n = k) (h2 : m = k)
    (f : Fin m → Fin n) (hf : ∀ i, (f i).val = i.val) :
    (fun i => Q (Fin.cast h1 (f i))) = fun i => Q (Fin.cast h2 i) := by
  funext i; congr 1; exact Fin.ext (by simp [hf])

/-- `Batch366.castMemTrace` of a package trace's family image is the family image at the other
tuple (both read `Qm` at the same column index). -/
theorem cast_familyQm (t t' : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    Batch366.castMemTrace P t t' (WrapMemoryConjuncts.familyQm P t Qm) =
      WrapMemoryConjuncts.familyQm P t' Qm :=
  castFin_gen Qm (FamilyComputeRows.memoryChipAt_width P t)
    (FamilyComputeRows.memoryChipAt_width P t') _ (fun _ => rfl)

/-- **The parallel chips read the IO pole.**  A memory trace accepted with some compute trace at a
twelve-coin tuple `c` is accepted with NO compute trace at `c` with the IO pole moved by one: the
twelve-coin memory chip at `c` is the landed memory chip at the memory view (`memSat_at_view`),
whose denominator-pin gate is linear in the pole (`Batch366.foreign_ioPole_rejects_succ`). -/
theorem parallel_rejected_at_foreign_pole
    (c : OptimizedProductionChallengeTuple12 K F)
    (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (hacc : PartAStaged.AcceptanceAt309 P Qc Qm c) :
    ∀ Qc' : Fin 309 → F[X],
      ¬ PartAStaged.AcceptanceAt309 P Qc' Qm (withIoPole12 c (c.2.1.2 + 1)) := by
  intro Qc' h'
  have h1 := PartAReWalk.memSat_at_view P Qc Qm c hacc
  have h2 := PartAReWalk.memSat_at_view P Qc' Qm _ h'
  rw [walkView11_withIoPole12] at h2
  have hpole : (walkView11 c).2.1.2 = c.2.1.2 := rfl
  have h3 := Batch366.foreign_ioPole_rejects_succ P (walkView11 c) _ h1
  rw [cast_familyQm, hpole] at h3
  exact h3 h2

theorem honest_rejected_at_foreign_pole12
    (QcH : Fin 309 → F[X]) (QmH : Fin P.memoryChip.rap.w → F[X])
    (hacc : PartAStaged.AcceptanceAt309 P QcH QmH (Pkg12.honestTuple12 P)) :
    withIoPole12 (Pkg12.honestTuple12 P) ((Pkg12.honestTuple12 P).2.1.2 + 1) ≠ Pkg12.honestTuple12 P ∧
      ∀ Qc : Fin 309 → F[X], ¬ PartAStaged.AcceptanceAt309 P Qc QmH
        (withIoPole12 (Pkg12.honestTuple12 P) ((Pkg12.honestTuple12 P).2.1.2 + 1)) :=
  ⟨withIoPole12_ne _, parallel_rejected_at_foreign_pole P _ QcH QmH hacc⟩

end Foreign

end

/-! ## (C4) reached, not used, at the new soundness roots -/

open Lean Meta Elab Command

def newRoots : List Name :=
  [ `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.acceptance_outside_failure_implies_target309,
    `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.optimizedFalseAcceptance309_probability_le,
    `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.stagedFalseAcceptance309_probability_le,
    `Nock.NockVMROM.Thm54.HostileSemanticSoundness.hostileSemanticSoundness_pinned ]

def realization309 : Name := `Nock.NockVMROM.Thm54.Unhosted309.OptimizedComputeRealizationAt309

/-- Uses of a structure `S` in an expression (projections by name or index, other constants under
`S`'s namespace), `Batch264.Audit.realizationUses` at a named structure. -/
partial def usesAt (S : Name) (e : Expr) : List String :=
  match e with
  | .const n _ => if S.isPrefixOf n && n != S then [s!"const {n.getString!}"] else []
  | .proj s i b => (if s == S then [s!"proj#{i}"] else []) ++ usesAt S b
  | .app f a => usesAt S f ++ usesAt S a
  | .lam _ t b _ => usesAt S t ++ usesAt S b
  | .forallE _ t b _ => usesAt S t ++ usesAt S b
  | .letE _ t v b _ => usesAt S t ++ usesAt S v ++ usesAt S b
  | .mdata _ b => usesAt S b
  | _ => []

def usesOfAt (env : Environment) (S n : Name) : List String :=
  match env.find? n with
  | none => []
  | some ci => usesAt S ci.type ++ (match ci.value? (allowOpaque := true) with
      | some v => usesAt S v | none => [])

open Nock.RedTeam.Batch264.Audit in
run_cmd do
  let env ← getEnv
  for r in newRoots do
    unless env.contains r do throwError "root missing: {r}"
  let R := reach env newRoots
  let w10 := `Nock.NockVMROM.Thm54.SampledIOSameExecutionAssignment.witness10_accepts
  let notReached := [`Nock.NockVMROM.Thm54.Unhosted309.canonical_satisfies309,
    `Nock.NockVMROM.Thm54.Unhosted309.correctedCanonicalFinalTrace309,
    `Nock.NockVMROM.Thm54.TraceGen.genBuildableOfProgram]
  unless R.contains w10 do throwError "[B1453 C4] instrument suspect: witness10_accepts not reached"
  for n in notReached do
    if R.contains n then throwError "[B1453 C4] STOP: the new roots reach {n}"
  let mut seen : List String := []
  for n in R do
    for S in [realizationStruct, realization309] do
      for u in usesOfAt env S n do
        unless allowedUses.contains u do
          throwError "[B1453 C4] STOP: {n} uses {S} ({u})"
        seen := s!"{S.getString!}.{u}" :: seen
  logInfo m!"[B1453 C4] reach set {R.size}; witness10_accepts reached; uses of the realization structures: {seen.eraseDups}; not reached: {notReached}"
  -- positive control: the honest-completeness theorem reaches what the soundness roots do not
  let pc := reach env [`Nock.RedTeam.Batch1431.gen_honest_accepted309]
  for n in [w10] ++ notReached do
    unless pc.contains n do throwError "[B1453 C4] positive control failed: {n}"
  logInfo m!"[B1453 C4] positive control gen_honest_accepted309 reaches {[w10] ++ notReached}"

end Nock.RedTeam.Batch1453

#check @Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompilesHostile
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompilesHostile
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
#print axioms Nock.NockVMROM.Thm54.HostileSemanticSoundness.hostileSemanticSoundness
#print axioms Nock.NockVMROM.Thm54.HostileSemanticSoundness.hostileSemanticSoundness_pinned
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.stagedFalseAcceptance309_probability_le
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.optimizedFalseAcceptance309_probability_le_two_pow_neg
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.acceptance_outside_failure_implies_target309
#print axioms Nock.RedTeam.Batch1420.gen_honest_accepted12
#print axioms Nock.RedTeam.Batch1431.gen_honest_accepted309
-- the figures at the swapped objects (the fifteen-summand bound function the statement now names)
#print axioms Nock.RedTeam.Batch1450.fig15_122
#print axioms Nock.RedTeam.Batch1450.fig15_120
#print axioms Nock.RedTeam.Batch1450.fig15_not_123
#print axioms Nock.RedTeam.Batch1450.fig15_paper_122
#print axioms Nock.RedTeam.Batch1450.fig15_ceiling_123
#print axioms Nock.RedTeam.Batch1453.honest_rejected_at_foreign_pole12
#print axioms Nock.RedTeam.Batch1453.parallel_rejected_at_foreign_pole
