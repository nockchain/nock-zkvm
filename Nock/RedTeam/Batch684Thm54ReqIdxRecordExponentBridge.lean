/-
  Nock/RedTeam/Batch684Thm54ReqIdxRecordExponentBridge.lean

  * **(1) the generated identification** (`generated_identification`): for any accepted program,
    at the generated α-free timestamp skeleton `genTimestampSkeleton`, on every `read_root` /
    `verify_child` row of a family whose rows are the generated execution's,
    `reqIdxNat R (memoryPubAt i) = (S.memoryRows[i]).recordExponent`.  Premises: the generator's
    capacity bounds and its own window `accAt … < orderOf α` (`nockCompiles`'s `hwin` implies it).
  * **(2) the generic bridge** (`generic_identification`): the same at any template `S` the rows
    specialize (compute/memory `…TimestampSpecializesAt`, origin `ln_prev = α^{lnPrev}`), under
    `L < orderOf α`, memory stamps `≤ L`, the paired layout and `C'` coherence; `read_root` rows
    need neither of the last two (`readRoot_identification`).
  * **(4) arithmetic illustration, not a control** (`window_is_load_bearing`): at `α = 1` the
    powers `α^1 = α^2` agree while `1 ≠ 2`.  No real control (a concrete family/row where two
    line numbers collide with `orderOf α ≤ L`) is exhibited.
  * **(5) the premises `hcr` / `hmr` are definitional for the production family**
    (`family_rows`).
  * **(6) the full composition** (`production_identification`): from
    `C : ExactFamilyCompletion (genBuildableOfProgram …) I` and `A` over `C.family` to the bridge.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenRecordExponentBridge

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch684

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.ForestExponentWindow
open Nock.NockVMROM.Thm54.RowLayout
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TraceGen.GenRecordExponentBridge
open Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization
open Nock.Framework.Thm54

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-- **(1)** F3 on the generated execution. -/
theorem generated_identification (A : SampledIOSameExecutionAssignment R p)
    (z α : K) (chal : ChallengeVector K) (hzc : chal.z = z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h) (a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α)
    (hcr : R.problem.exec.computeRows =
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).computeRows)
    (hmr : R.problem.exec.memoryRows =
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).memoryRows)
    (i : Fin R.problem.cfg.memRows)
    (hi : (i : ℕ) < (genTimestampSkeleton F (airReorder t)
      (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))
      (genComputeSkeleton_memForest_stampsWellFormed z α h)).memoryRows.length)
    (hlive : (R.problem.exec.memoryPubAt i).st = .read_root ∨
      (R.problem.exec.memoryPubAt i).st = .verify_child) :
    reqIdxNat R (R.problem.exec.memoryPubAt i) =
      ((genTimestampSkeleton F (airReorder t)
        (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))
        (genComputeSkeleton_memForest_stampsWellFormed z α h)).memoryRows[(i : ℕ)]'hi).recordExponent :=
  generated_reqIdxNat_eq_recordExponent A z α chal hzc Ksz orbit horb a b c h hmempos hcomp hmem
    horbα hcr hmr i hi hlive

/-- **(2)** The generic bridge on every live row. -/
theorem generic_identification (A : SampledIOSameExecutionAssignment R p)
    {base : SemanticSkeleton} (S : SemanticTimestampSkeleton F K base) {α : K}
    (hts : List.Forall₂ (ComputeTimestampSpecializesAt α) S.computeRows
      R.problem.exec.computeRows)
    (hor : List.Forall₂ (fun stamp row => row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
      S.computeRows R.problem.exec.computeRows)
    (hmts : List.Forall₂ (MemoryTimestampSpecializesAt α) S.memoryRows
      R.problem.exec.memoryRows)
    (hwin : totalRecordCount S.computeRows < orderOf α)
    (hmemle : ∀ stamp ∈ S.memoryRows, stamp.recordExponent ≤ totalRecordCount S.computeRows)
    (hprl : PairedRecordLayout R.problem.exec) (hC : R.problem.exec.CprimeCoherent)
    (i : Fin R.problem.cfg.memRows) (hi : (i : ℕ) < S.memoryRows.length)
    (hlive : (R.problem.exec.memoryPubAt i).st = .read_root ∨
      (R.problem.exec.memoryPubAt i).st = .verify_child) :
    reqIdxNat R (R.problem.exec.memoryPubAt i) = (S.memoryRows[(i : ℕ)]'hi).recordExponent :=
  reqIdxNat_eq_recordExponent_live A S hts hor hmts hwin hmemle hprl hC i hi hlive

/-- **(2′)** `read_root` rows: no layout and no coherence premise. -/
theorem readRoot_identification (A : SampledIOSameExecutionAssignment R p)
    {base : SemanticSkeleton} (S : SemanticTimestampSkeleton F K base) {α : K}
    (hts : List.Forall₂ (ComputeTimestampSpecializesAt α) S.computeRows
      R.problem.exec.computeRows)
    (hor : List.Forall₂ (fun stamp row => row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
      S.computeRows R.problem.exec.computeRows)
    (hmts : List.Forall₂ (MemoryTimestampSpecializesAt α) S.memoryRows
      R.problem.exec.memoryRows)
    (hwin : totalRecordCount S.computeRows < orderOf α)
    (hmemle : ∀ stamp ∈ S.memoryRows, stamp.recordExponent ≤ totalRecordCount S.computeRows)
    (i : Fin R.problem.cfg.memRows) (hi : (i : ℕ) < S.memoryRows.length)
    (hst : (R.problem.exec.memoryPubAt i).st = .read_root) :
    reqIdxNat R (R.problem.exec.memoryPubAt i) = (S.memoryRows[(i : ℕ)]'hi).recordExponent :=
  reqIdxNat_eq_recordExponent_readRoot A S hts hor hmts hwin hmemle i hi hst

theorem position_is_template_exponent
    {base : SemanticSkeleton} (S : SemanticTimestampSkeleton F K base) {α lmb : K}
    {rows : List (ComputeTable.State × ComputeTable.DTcomp K)}
    (hts : List.Forall₂ (ComputeTimestampSpecializesAt α) S.computeRows rows)
    (hor : List.Forall₂ (fun stamp row => row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
      S.computeRows rows)
    (hnd : (rows.flatMap fun row =>
      (NockVM.activeRequestRecords row.2.2.1).map fun r => NockVM.encRecFormR r lmb).Nodup)
    {x : Fin 9 → K}
    (hx : x ∈ rows.flatMap fun row =>
      (NockVM.activeRequestRecords row.2.2.1).map fun r => NockVM.encRecFormR r lmb) :
    ∃ stamp ∈ S.computeRows, ∃ i : Fin 3,
      (i : ℕ) < Nock.Framework.recordCount stamp.state ∧
      RecordCarrier.honestExp (rows.flatMap fun row =>
        (NockVM.activeRequestRecords row.2.2.1).map fun r => NockVM.encRecFormR r lmb) x =
          stamp.recordExponent i ∧
      x 7 = α ^ stamp.recordExponent i :=
  request_honestExp_eq_recordExponent S hts hor hnd hx

/-- **(4)** Arithmetic illustration only, NOT a control on the bridge: at `α = 1` (`orderOf 1 = 1`)
the powers `α^1 = α^2` agree while `1 ≠ 2`, i.e. a timestamp slot `α^e` determines `e` only
inside `orderOf α`.  No real control exists in this batch: no concrete family/row is exhibited on
which two line numbers collide with `orderOf α ≤ L` and the bridge's conclusion fails. -/
theorem window_is_load_bearing :
    (1 : ℚ) ^ (1 : ℕ) = (1 : ℚ) ^ (2 : ℕ) ∧ (1 : ℕ) ≠ 2 ∧ ¬ ((2 : ℕ) < orderOf (1 : ℚ)) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [orderOf_one]; norm_num

/-- **(5)** The production family's rows are its carrier's rows, definitionally: `hcr` / `hmr` of
(1) hold by `rfl` for `ExactFamilyCompletion.family` (the family `BuildableChips` builds over
`E`); for `E = genBuildableOfProgram …`, `E.exec` is `genExactExecution …` by `change`
(`genBuildableOfProgram_pairedRecordLayout`). -/
theorem family_rows {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    {E : BuildableNockExecution F K} {I : BuildableChips.Inputs E}
    (C : BuildableChips.ExactFamilyCompletion E I) :
    C.family.problem.exec.computeRows = E.exec.computeRows ∧
      C.family.problem.exec.memoryRows = E.exec.memoryRows :=
  ⟨rfl, rfl⟩

/-- **(6)** The full composition: from `C : ExactFamilyCompletion (genBuildableOfProgram …) I` and
`A` over `C.family` to the bridge, with `hzc` from `hinp`, `horbα` from `hB`/`hwin`, and
`hcr`/`hmr` by `rfl` (`GenRecordExponentBridge.production_reqIdxNat_eq_recordExponent`). -/
theorem production_identification {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {q Λ : ℕ}
    (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hseed : SeedGood z t)
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder t))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz)
    (hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz)
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q)
    (hq : 11 < q) (hchar : q = ringChar K)
    (haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)))
    (hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t)))
    (hKszChar : Ksz < ringChar K)
    (hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h)
    (hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h)
    (hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    {I : BuildableChips.Inputs (genBuildableOfProgram (F := F) z α hz htwo a b c chal hinp hmi Ksz orbit horb
        h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst)}
    (C : BuildableChips.ExactFamilyCompletion _ I)
    (A : SampledIOSameExecutionAssignment C.family (ringChar K))
    (i : Fin C.family.problem.cfg.memRows)
    (hi : (i : ℕ) < (genTimestampSkeleton F (airReorder t)
      (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))
      (genComputeSkeleton_memForest_stampsWellFormed z α h)).memoryRows.length)
    (hlive : (C.family.problem.exec.memoryPubAt i).st = MemoryTable.MState.read_root ∨
      (C.family.problem.exec.memoryPubAt i).st = MemoryTable.MState.verify_child) :
    reqIdxNat C.family (C.family.problem.exec.memoryPubAt i) =
      ((genTimestampSkeleton F (airReorder t)
        (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))
        (genComputeSkeleton_memForest_stampsWellFormed z α h)).memoryRows[(i : ℕ)]'hi).recordExponent :=
  production_reqIdxNat_eq_recordExponent z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed
    hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar
    hprogCap hmemCap hfirst C A i hi hlive

end Nock.RedTeam.Batch684

#print axioms Nock.RedTeam.Batch684.generated_identification
#print axioms Nock.RedTeam.Batch684.generic_identification
#print axioms Nock.RedTeam.Batch684.readRoot_identification
#print axioms Nock.RedTeam.Batch684.position_is_template_exponent
#print axioms Nock.RedTeam.Batch684.window_is_load_bearing
#print axioms Nock.RedTeam.Batch684.family_rows
#print axioms Nock.RedTeam.Batch684.production_identification
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenRecordExponentBridge.generated_reqIdxNat_eq_recordExponent
