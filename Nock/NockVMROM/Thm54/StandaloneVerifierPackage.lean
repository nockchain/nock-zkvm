/-
  Nock/NockVMROM/Thm54/StandaloneVerifierPackage.lean

  Section `Package` of `StandaloneVerifierData.lean`
  (`ofPackage`, `msgsOf`, `msgsOfTraces`, `coord_equivFun_symm`, `coord_of_sum`, `pubC_ofPackage`,
  `pubM_ofPackage`, `chipsOf_ofPackage`, `chipsOf_ofPackage_traces`, `msgsOfTraces_staged`), moved
  verbatim (names, docstrings, statements and proofs unchanged; only the file-level `set_option` /
  namespace / `open` / `noncomputable section` context is re-opened here).
-/
import Nock.NockVMROM.Thm54.StandaloneVerifierData
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events
import Nock.NockVMROM.Thm54.GeneratedField
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.StandaloneVerifier

open Nock Nock.Framework Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.PartA12
open Module
open scoped Polynomial

noncomputable section

/-! ## 5. The package is an instance -/

section Package

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The verifier data a package carries. -/
def ofPackage : VerifierData F K hOrb where
  claim := P.optimized.verifier.raw.claim
  N := P.optimized.family.problem.cfg.compRows
  M := P.optimized.family.problem.cfg.memRows
  kMem := P.optimized.family.problem.cfg.kMem
  Ksz := P.optimized.family.problem.cfg.Ksz
  hN := P.optimized.family.problem.cfg.compRows_pos
  hM := P.optimized.family.problem.cfg.memRows_pos
  basis := P.optimized.basis
  orbit := P.optimized.orbit
  computeNodes := P.optimized.computeNodes
  memoryNodes := P.optimized.memoryNodes

/-- The messages a package's (coin-constant) prover sends.  `requests c` is the sampled IO
terminal (constant), the seed is the package's memory publics `9..11` reassembled in `𝕂`. -/
def msgsOf : Messages F K (currentMemFamily (F := F) (K := K) hOrb) where
  Qc := fun _ _ => 0
  Qm := fun _ _ => 0
  lastState := fun j => P.optimized.computePublic (31 + (j : ℕ))
  restC := P.optimized.computePublic
  memMsg0 := P.optimized.memoryPublic
  requests := fun _ => P.optimized.sampled.witness10.terminal
  memMsg2 := fun _ =>
    P.optimized.basis.equivFun.symm (fun k => P.optimized.memoryPublic (9 + (k : ℕ)))

/-- `msgsOf` with the package's traces `Qc`/`Qm` substituted (constant strategy). -/
def msgsOfTraces (Qc : Fin 309 → F[X]) (Qm : Fin 205 → F[X]) :
    Messages F K (currentMemFamily (F := F) (K := K) hOrb) :=
  { msgsOf P with Qc := fun _ => Qc, Qm := fun _ => Qm }

omit [DecidableEq F] [CharP K (ringChar K)] in
theorem coord_equivFun_symm (b : Basis (Fin 3) F K) (x : Fin 3 → F) (k : Fin 3) :
    coord b (b.equivFun.symm x) k = x k := by
  unfold coord
  rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

omit [DecidableEq F] [CharP K (ringChar K)] in
theorem coord_of_sum (b : Basis (Fin 3) F K) (x : Fin 3 → F) (y : K)
    (hy : (∑ k : Fin 3, x k • b k) = y) (k : Fin 3) : x k = coord b y k := by
  rw [← hy, ← Basis.equivFun_symm_apply, coord_equivFun_symm]

/-- The compute public map the standalone verifier builds at `ofPackage P` / `msgsOf P` IS the
package's, under N4 (`hst`). -/
theorem pubC_ofPackage
    (hst : (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).state =
      ComputeWalkSeed.rootStateOfFormula P.optimized.verifier.raw.claim.formula)
    (c : Tuple12 K F) :
    pubC (ofPackage P) (msgsOf P) c = P.optimized.computePublic := by
  funext j
  unfold pubC
  by_cases h1 : 6 ≤ j ∧ j < 9
  · rw [dif_pos h1]
    have := P.optimized.computeRequestsPins ⟨j - 6, by omega⟩
    simp only [show 6 + (j - 6) = j by omega] at this
    exact this.symm
  rw [dif_neg h1]
  by_cases h2 : 20 ≤ j ∧ j < 31
  · rw [dif_pos h2]
    have := P.optimized.computePublicPins.2.1 ⟨j - 20, by omega⟩
    simp only [show 20 + (j - 20) = j by omega] at this
    rw [this, hst]
    rfl
  rw [dif_neg h2]
  by_cases h3 : 31 ≤ j ∧ j < 42
  · rw [dif_pos h3]
    show P.optimized.computePublic (31 + (j - 31)) = _
    rw [show 31 + (j - 31) = j by omega]
  rw [dif_neg h3]
  rfl

/-- The memory public map at `ofPackage P` / `msgsOf P` IS the package's (no hypothesis). -/
theorem pubM_ofPackage :
    pubMCurrent (ofPackage P) P.optimized.memoryPublic P.optimized.sampled.witness10.terminal
        (P.optimized.basis.equivFun.symm (fun k => P.optimized.memoryPublic (9 + (k : ℕ)))) =
      P.optimized.memoryPublic := by
  funext j
  unfold pubMCurrent
  by_cases h1 : 9 ≤ j ∧ j < 12
  · rw [dif_pos h1]
    show coord P.optimized.basis _ _ = _
    rw [coord_equivFun_symm]
    simp only [show 9 + (j - 9) = j by omega]
  rw [dif_neg h1]
  by_cases h2 : 12 ≤ j ∧ j < 15
  · rw [dif_pos h2]
    have := coord_of_sum P.optimized.basis
      (fun k => P.optimized.memoryPublic (6 + 3 * 2 + (k : ℕ))) _
      P.optimized.memoryCoordinatePins.requests ⟨j - 12, by omega⟩
    simp only [show 6 + 3 * 2 + (j - 12) = j by omega] at this
    exact this.symm
  rw [dif_neg h2]

/-- Not `rfl`: proved through `pubC_ofPackage` /
`pubM_ofPackage`; the only hypothesis is N4 (`hst`). -/
theorem chipsOf_ofPackage
    (hst : (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).state =
      ComputeWalkSeed.rootStateOfFormula P.optimized.verifier.raw.claim.formula)
    (c : Tuple12 K F) :
    chipsOf (ofPackage P) (msgsOf P) c =
      (Unhosted309.pkgComputeChipAt309 P (forget12 c), Pkg12.memoryChipAt12 P c) := by
  have hC := pubC_ofPackage P hst c
  have hM := pubM_ofPackage P
  unfold chipsOf
  rw [hC]
  change (_, DeployedChipFamily12.memoryChipAt12 _ _ _
      (memoryPublicOfTuple12 _ _ _ (pubMCurrent (ofPackage P) P.optimized.memoryPublic
        P.optimized.sampled.witness10.terminal
        (P.optimized.basis.equivFun.symm fun k => P.optimized.memoryPublic (9 + (k : ℕ)))) c)
      _ c _) = _
  rw [hM]
  rfl

/-- The same at the package's traces (the messages only differ in the column fields). -/
theorem chipsOf_ofPackage_traces
    (hst : (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).state =
      ComputeWalkSeed.rootStateOfFormula P.optimized.verifier.raw.claim.formula)
    (Qc : Fin 309 → F[X]) (Qm : Fin 205 → F[X]) (c : Tuple12 K F) :
    chipsOf (ofPackage P) (msgsOfTraces P Qc Qm) c =
      (Unhosted309.pkgComputeChipAt309 P (forget12 c), Pkg12.memoryChipAt12 P c) :=
  chipsOf_ofPackage P hst c

/-- The package's prover messages are staged (constant traces). -/
theorem msgsOfTraces_staged (Qc : Fin 309 → F[X]) (Qm : Fin 205 → F[X]) :
    StagedV (msgsOfTraces P Qc Qm) :=
  ⟨staged12_const _ Qc, staged12_const _ Qm⟩

end Package

end

end Nock.NockVMROM.Thm54.StandaloneVerifier
