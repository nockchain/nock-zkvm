/-
  Nock/RedTeam/Batch1063Thm54RepairIIWindow.lean

  * The signed §1 `hwin` is `programAcc t + 3 < orderOf α ∧ programMemShape α t ≤ orderOf α`
    (`GenNockCompilesCarrier.lean::nockCompiles_zmod`).  `old_hwin_of_weakest`: it subsumes the
    old `hwin` (its first conjunct).
  * The fit form `programFit α t + 2 < orderOf α` (the pre-greenlight's recommendation, NOT
    signed) implies the weakest one (`weakest_of_fit`); its halves and the converse
    `programFit_window_of_parts` are kept as the record of that comparison.  The two forms
    differ exactly on four orders (`Batch1062.narrowing_window`, `_sharp`; reached at fib,
    `Batch1210`).
  * `hordM_of_window` / `hordM_of_weakest`: `buildFullPackage`'s `hordM` at `mwa := α`, in the
    chain's own binder shape (`inputsOfCarrier … cwa α wg msc mef …`), discharged from the §1
    pair and from the bare `memRows ≤ orderOf α`, through the production helper
    `TraceGen.memRowsL_le_orderOf_of_shape` (the same helper the 18 chain discharges use).
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Nock.RedTeam.Batch1063

open Nock Nock.Walk
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.TraceGen

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]

/-! ## A. The strengthened window and its two halves -/

theorem programAcc_window_of_fit {α : K} {t : NTree (GenComputeRow K)}
    (h : programFit α t + 2 < orderOf α) : programAcc t + 3 < orderOf α := by
  have := programAcc_succ_le_fit α t
  omega

theorem programMemShape_window_of_fit {α : K} {t : NTree (GenComputeRow K)}
    (h : programFit α t + 2 < orderOf α) : programMemShape α t + 3 < orderOf α := by
  have := programMemShape_succ_le_fit α t
  omega

/-- The fit form is exactly the conjunction of its two halves (`compRows ≤ acc`). -/
theorem programFit_window_of_parts {α : K} {t : NTree (GenComputeRow K)}
    (hacc : programAcc t + 3 < orderOf α) (hmem : programMemShape α t + 3 < orderOf α) :
    programFit α t + 2 < orderOf α := by
  have hc : programCompRows t + 2 < orderOf α := by
    have := programAcc_ge_compRows t
    unfold programCompRows
    omega
  have hfit : programFit α t < orderOf α - 2 :=
    max_lt (max_lt (by omega) (by omega)) (by omega)
  omega

/-- The old `hwin` is a corollary: the fit form subsumes it. -/
theorem old_hwin_of_fit {α : K} {t : NTree (GenComputeRow K)}
    (h : programFit α t + 2 < orderOf α) : programAcc t + 3 < orderOf α :=
  programAcc_window_of_fit h

/-- The fit form implies the signed weakest form (so the weakest form is the weaker
hypothesis). -/
theorem weakest_of_fit {α : K} {t : NTree (GenComputeRow K)}
    (h : programFit α t + 2 < orderOf α) :
    programAcc t + 3 < orderOf α ∧ programMemShape α t ≤ orderOf α :=
  ⟨programAcc_window_of_fit h, by have := programMemShape_window_of_fit h; omega⟩

/-- **The signed `hwin` subsumes the old one** (its first conjunct). -/
theorem old_hwin_of_weakest {α : K} {t : NTree (GenComputeRow K)}
    (h : programAcc t + 3 < orderOf α ∧ programMemShape α t ≤ orderOf α) :
    programAcc t + 3 < orderOf α :=
  h.1

/-! ## B. The consumer obligation, at the chain's own shape -/

section Generated

variable {q Λ : ℕ}
    {z α : K} {hz : z ≠ 0} {htwo : (2 : K) ≠ 0} {a b c : K}
    {chal : ChallengeVector K} {hinp : chal.computeInputs = ⟨α, z, a, b, c⟩}
    {hmi : chal.memoryInputs = memInputs z}
    {Ksz : ℕ} {orbit : OrbitDomain K} {horb : 1 ≤ orbit.h}
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    {h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)}
    {hseed : SeedGood z t}
    {hcoins : ComputeCoinsGeneric z α a b c (airReorder t)}
    {hΛ : 1 ≤ Λ} {hconf : TraceConfined Λ (airReorder t)}
    {hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length}
    {hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h}
    {hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h}
    {B : ℕ} {hB : B ≤ orderOf α}
    {hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B}
    {hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz}
    {hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz}
    {hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q}
    {hq : 11 < q} {hchar : q = ringChar K}
    {haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t))}
    {hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds}
    {hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t))}
    {hKszChar : Ksz < ringChar K}
    {hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h}
    {hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h}
    {hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K}




/-- **`hordM` at `mwa := α`**, discharged from the second conjunct of the signed §1 `hwin`: the
one obligation repair (ii) adds (18 discharge sites in `GenNockCompilesBounded`, all of this
shape). -/
theorem hordM_of_window
    (stc : NodeEncoding.StateTagChar K) (bas : Module.Basis (Fin 3) F K) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (msc : Fin 4 → F) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hwin' : programAcc t + 3 < orderOf α ∧ programMemShape α t ≤ orderOf α) :
    2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤
      orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
        chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
        hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq
        hresp hcard cwa α wg msc mef hinterCard hhon).memoryWalkAlpha := by
  intro _
  change (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ orderOf α
  exact TraceGen.memRowsL_le_orderOf_of_shape hwin'.2

/-- The same from the WEAKEST sufficient condition, `memRows ≤ orderOf α` itself. -/
theorem hordM_of_weakest
    (stc : NodeEncoding.StateTagChar K) (bas : Module.Basis (Fin 3) F K) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (msc : Fin 4 → F) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hweak : programMemShape α t ≤ orderOf α) :
    2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤
      orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
        chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
        hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq
        hresp hcard cwa α wg msc mef hinterCard hhon).memoryWalkAlpha := by
  intro _
  change (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ orderOf α
  change programMemRowsL chal.lam z α t ≤ orderOf α
  rw [← programMemShape_spec (lmb := chal.lam) z α t]
  exact hweak

end Generated

end

end Nock.RedTeam.Batch1063

#print axioms Nock.RedTeam.Batch1063.programFit_window_of_parts
#print axioms Nock.RedTeam.Batch1063.weakest_of_fit
#print axioms Nock.RedTeam.Batch1063.old_hwin_of_weakest
#print axioms Nock.RedTeam.Batch1063.hordM_of_window
#print axioms Nock.RedTeam.Batch1063.hordM_of_weakest
