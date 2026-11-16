import Nock.RedTeam.Batch1964Thm54VclCompletenessChosen
import Nock.NockVMROM.Thm54.VclL.Compute.TowerPackageW
import Nock.NockVMROM.Thm54.Walk39.OptimizedStrictFullPackage

/-!
Compiles a run of the Nock VM into the capstone package at the walk instance: from a successful
evaluation `hrun` (within the field bound `hbound`) it builds the full strict package and concludes
the capstone statement `optimizedFullStrictNockVMROM_of_package`.  The tower parameter `δ` is chosen
as a base non-square of `F` (lifted to `K` by `T0Tower.nonsquare_lift`), the table heights are chosen
from the run (`heightOf`), and the honest datum is `honestVCLJW_of_run`.

* `nockCompiles_p76` is the statement for a general finite field `F` with `2^63 < char F`
  (`hq`); the inequality `25 ≤ char F` is derived from it.
* `nockCompiles_zmod` and `nockCompilesHostile` are the statements for `F = ZMod p`.
-/

open Nock Nock.NockVMROM Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.TraceGen
namespace Nock.Walk39

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen.VCL38

open Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Compute.TowerChosen Nock.NockVMROM.Thm54.VclL.Events
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage

noncomputable section

attribute [local instance] ringCharFactW algZModW

/-! ## 1. The chosen base non-square, generic in `F` -/

section Delta
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem two_ne_of_hq (hq : 2 ^ 63 < ringChar F) : ringChar F ≠ 2 := by
  have : (2 : ℕ) ≤ 2 ^ 63 := by norm_num
  omega

theorem hp_of_hq (hq : 2 ^ 63 < ringChar F) : 25 ≤ ringChar F := by
  have : (25 : ℕ) ≤ 2 ^ 63 := by norm_num
  omega

theorem exists_nonsquare_ne_zero_F (h2 : ringChar F ≠ 2) : ∃ d : F, d ≠ 0 ∧ ¬ IsSquare d := by
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare h2
  exact ⟨a, fun h => ha (h ▸ ⟨0, by simp⟩), ha⟩

/-- The chosen base non-square (needs only `2^63 < char F`). -/
def δc (hq : 2 ^ 63 < ringChar F) : F :=
  Classical.choose (exists_nonsquare_ne_zero_F (two_ne_of_hq hq))

theorem δc_spec (hq : 2 ^ 63 < ringChar F) : δc hq ≠ 0 ∧ ¬ IsSquare (δc hq) :=
  Classical.choose_spec (exists_nonsquare_ne_zero_F (two_ne_of_hq hq))

/-- The chosen `δ` stays a non-square in any cubic extension `K` (`T0Tower.nonsquare_lift`). -/
theorem δc_nonsquare {K : Type} [Field K] [Algebra F K] [Fintype K]
    (hq : 2 ^ 63 < ringChar F) (hK3 : Module.finrank F K = 3) :
    ¬ IsSquare (algebraMap F K (δc hq)) :=
  T0Tower.nonsquare_lift (F := F) (K := K) (two_ne_of_hq hq)
    (by rw [← Algebra.ringChar_eq F K]; exact two_ne_of_hq hq) hK3 _ (δc_spec hq).1 (δc_spec hq).2

end Delta

/-! ## 2. The chosen heights, generic in `F` -/

section Heights
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  {fuel : ℕ} {subject formula result : Noun}
  (hrun : Nock.evalN fuel subject formula = some result)
  (hbound : RunBoundedBy (ringChar F) fuel subject formula)

/-- Chosen compute height. -/
def hCg : ℕ := heightOf (nRows (runTree (K := K) δF hrun hbound))
/-- Chosen cell-table height. -/
def hTg : ℕ := heightOf (cellLen (K := K) δF (runTree (K := K) δF hrun hbound))
/-- Chosen path-chip height. -/
def hPg : ℕ := heightOf (pathLen (K := K) δF (runTree (K := K) δF hrun hbound))

/-- **The package built from the run** at the chosen heights. -/
def pkgOfRun [CharP K (ringChar K)] (hK3 : Module.finrank F K = 3) (hq : 2 ^ 63 < ringChar F)
    (hFprime : GeneratedField.PrimeFieldElems F)
    (hF : 3 * 2 ^ (max (hCg (K := K) δF hrun hbound)
        (max (hTg (K := K) δF hrun hbound) (hPg (K := K) δF hrun hbound))) ∣ Fintype.card F - 1)
    (hrowsC : 3 * nRows (runTree (K := K) δF hrun hbound) < ringChar F)
    (hmemC : cellLen (K := K) δF (runTree (K := K) δF hrun hbound) + 1 < ringChar F)
    (hmemW : krW (demT (runTree (K := K) δF hrun hbound)).cells (demT (runTree (K := K) δF hrun hbound)).preads +
      (walkRows (demT (runTree (K := K) δF hrun hbound)).cells
        (demT (runTree (K := K) δF hrun hbound)).preads).length < ringChar F)
    (hleaf : programLeafBound (airReorder (runTree (K := K) δF hrun hbound)) ≤ 2 ^ 110)
    (haxis : programAxisBound (airReorder (runTree (K := K) δF hrun hbound)) < 2 ^ 63) :
    OptimizedFullStrictNockVMROMPackage F K (hCg (K := K) δF hrun hbound) where
  δ := δF
  hT := hTg (K := K) δF hrun hbound
  hP := hPg (K := K) δF hrun hbound
  honest := honestVCLJW_of_run (K := K) δF _ _ _ hrun hbound 0 0 hK3 (hp_of_hq hq)
    (one_le_heightOf _) (one_le_heightOf _) (one_le_heightOf _)
    (orbit_dvd_split hF).1 (orbit_dvd_split hF).2.1 (orbit_dvd_split hF).2.2
    (le_two_pow_heightOf _) (by rw [← Algebra.ringChar_eq F K]; exact hrowsC)
    (le_two_pow_heightOf _) (le_two_pow_heightOf _)
  primeField := hFprime
  char_gt := hq
  hleaf := hleaf
  hmemRows := memRowsW_of_run (K := K) δF _ _ _ hrun hbound 0 hK3
    (one_le_heightOf _) (one_le_heightOf _) (one_le_heightOf _)
    (orbit_dvd_split hF).1 (orbit_dvd_split hF).2.1 (orbit_dvd_split hF).2.2 hmemC hmemW
  haxis := haxis
  hkp := kpW_of_run (K := K) δF _ _ _ hrun hbound 0 hK3
    (one_le_heightOf _) (one_le_heightOf _) (one_le_heightOf _)
    (orbit_dvd_split hF).1 (orbit_dvd_split hF).2.1 (orbit_dvd_split hF).2.2 hmemW

end Heights

/-! ## 3. `nockCompiles_p76` (general `F`, 28/15) -/

theorem nockCompiles_p76 {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    {fuel : ℕ} {subject formula result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar F) fuel subject formula)
    (hs : FieldEmbedding.BoundedBy (ringChar F) subject)
    (hf : FieldEmbedding.BoundedBy (ringChar F) formula)
    (hK3 : Module.finrank F K = 3) (hq : 2 ^ 63 < ringChar F)
    (hFprime : GeneratedField.PrimeFieldElems F) :
    haveI : Fact (¬ IsSquare (algebraMap F K (δc hq))) := ⟨δc_nonsquare hq hK3⟩
    ∀ (hF : 3 * 2 ^ (max (hCg (K := K) (δc hq) hrun hbound)
        (max (hTg (K := K) (δc hq) hrun hbound) (hPg (K := K) (δc hq) hrun hbound))) ∣
          Fintype.card F - 1)
      (hrowsC : 3 * nRows (runTree (K := K) (δc hq) hrun hbound) < ringChar F)
      (hmemC : cellLen (K := K) (δc hq) (runTree (K := K) (δc hq) hrun hbound) + 1 < ringChar F)
      (hmemW : krW (demT (runTree (K := K) (δc hq) hrun hbound)).cells
          (demT (runTree (K := K) (δc hq) hrun hbound)).preads +
        (walkRows (demT (runTree (K := K) (δc hq) hrun hbound)).cells
          (demT (runTree (K := K) (δc hq) hrun hbound)).preads).length < ringChar F)
      (hleaf : programLeafBound (airReorder (runTree (K := K) (δc hq) hrun hbound)) ≤ 2 ^ 110)
      (haxis : programAxisBound (airReorder (runTree (K := K) (δc hq) hrun hbound)) < 2 ^ 63),
    ∃ package : OptimizedFullStrictNockVMROMPackage F K (hCg (K := K) (δc hq) hrun hbound),
      OptimizedFullStrictThm54Statement package ∧
        package.honest.V.claim = ⟨subject, formula, result⟩ := by
  intro hF hrowsC hmemC hmemW hleaf haxis
  haveI : Fact (¬ IsSquare (algebraMap F K (δc hq))) := ⟨δc_nonsquare hq hK3⟩
  exact ⟨pkgOfRun (K := K) (δc hq) hrun hbound hK3 hq hFprime hF hrowsC hmemC hmemW hleaf haxis,
    optimizedFullStrictNockVMROM_of_package _, rfl⟩

/-! ## 4. `nockCompiles_zmod` (`F = ZMod p`, 25/15) -/

section Zmod
variable {p : ℕ} [Fact p.Prime]

theorem hqz (hq : 2 ^ 63 < p) : 2 ^ 63 < ringChar (ZMod p) := by
  rw [ZMod.ringChar_zmod_n]; exact hq

theorem hbz {fuel : ℕ} {subject formula : Noun} (hbound : RunBoundedBy p fuel subject formula) :
    RunBoundedBy (ringChar (ZMod p)) fuel subject formula := by
  rw [ZMod.ringChar_zmod_n]; exact hbound

end Zmod

theorem nockCompiles_zmod {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    [FiniteDimensional (ZMod p) K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    {fuel : ℕ} {subject formula result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy p fuel subject formula)
    (hs : FieldEmbedding.BoundedBy p subject) (hf : FieldEmbedding.BoundedBy p formula)
    (hK3 : Module.finrank (ZMod p) K = 3) (hq : 2 ^ 63 < p) :
    haveI : Fact (¬ IsSquare (algebraMap (ZMod p) K (δc (hqz hq)))) := ⟨δc_nonsquare (hqz hq) hK3⟩
    ∀ (hF : 3 * 2 ^ (max (hCg (K := K) (δc (hqz hq)) hrun (hbz hbound))
        (max (hTg (K := K) (δc (hqz hq)) hrun (hbz hbound))
          (hPg (K := K) (δc (hqz hq)) hrun (hbz hbound)))) ∣ p - 1)
      (hrowsC : 3 * nRows (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound)) < p)
      (hmemC : cellLen (K := K) (δc (hqz hq)) (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound)) + 1 < p)
      (hmemW : krW (demT (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))).cells
          (demT (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))).preads +
        (walkRows (demT (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))).cells
          (demT (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))).preads).length < p)
      (hleaf : programLeafBound (airReorder (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))) ≤ 2 ^ 110)
      (haxis : programAxisBound (airReorder (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))) < 2 ^ 63),
    ∃ package : OptimizedFullStrictNockVMROMPackage (ZMod p) K
        (hCg (K := K) (δc (hqz hq)) hrun (hbz hbound)),
      OptimizedFullStrictThm54Statement package ∧
        package.honest.V.claim = ⟨subject, formula, result⟩ := by
  intro hF hrowsC hmemC hmemW hleaf haxis
  have hr : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hs' : FieldEmbedding.BoundedBy (ringChar (ZMod p)) subject := by rw [hr]; exact hs
  have hf' : FieldEmbedding.BoundedBy (ringChar (ZMod p)) formula := by rw [hr]; exact hf
  have hF' := hF
  rw [show p - 1 = Fintype.card (ZMod p) - 1 by rw [ZMod.card]] at hF'
  exact nockCompiles_p76 (F := ZMod p) (K := K) hrun (hbz hbound) hs' hf' hK3 (hqz hq)
    (GeneratedField.primeFieldElems_zmod p) hF' (by rw [hr]; exact hrowsC) (by rw [hr]; exact hmemC)
    (by rw [hr]; exact hmemW) hleaf haxis

/-! ## 5. `nockCompilesHostile` (25/15): the staged bound at the compiler-built verifier -/

open Classical in
theorem nockCompilesHostile {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    [FiniteDimensional (ZMod p) K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    {fuel : ℕ} {subject formula result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy p fuel subject formula)
    (hs : FieldEmbedding.BoundedBy p subject) (hf : FieldEmbedding.BoundedBy p formula)
    (hK3 : Module.finrank (ZMod p) K = 3) (hq : 2 ^ 63 < p) :
    haveI : Fact (¬ IsSquare (algebraMap (ZMod p) K (δc (hqz hq)))) := ⟨δc_nonsquare (hqz hq) hK3⟩
    ∀ (hF : 3 * 2 ^ (max (hCg (K := K) (δc (hqz hq)) hrun (hbz hbound))
        (max (hTg (K := K) (δc (hqz hq)) hrun (hbz hbound))
          (hPg (K := K) (δc (hqz hq)) hrun (hbz hbound)))) ∣ p - 1)
      (hrowsC : 3 * nRows (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound)) < p)
      (hmemC : cellLen (K := K) (δc (hqz hq)) (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound)) + 1 < p)
      (hmemW : krW (demT (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))).cells
          (demT (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))).preads +
        (walkRows (demT (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))).cells
          (demT (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))).preads).length < p)
      (hleaf : programLeafBound (airReorder (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))) ≤ 2 ^ 110)
      (haxis : programAxisBound (airReorder (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))) < 2 ^ 63),
    ∃ package : OptimizedFullStrictNockVMROMPackage (ZMod p) K
        (hCg (K := K) (δc (hqz hq)) hrun (hbz hbound)),
      OptimizedFullStrictThm54Statement package ∧
        package.honest.V.claim = ⟨subject, formula, result⟩ ∧
        ∀ msg : Messages package.CF package.MF, msg.Staged →
          package.verifier.Checks (consumerBound package.CF package.MF package.verifier)
            (ringChar package.FP) →
          ((Finset.univ.filter fun χ : Coins frameVCL K =>
              AcceptsV package.verifier msg χ ∧
                ¬ SVGenuineF.HoldsF (ringChar K) package.verifier.claim).card : ℚ) /
              Fintype.card (Coins frameVCL K) ≤
            boundVCLW'' (Fintype.card K) package.verifier.N (cellRows package.verifier)
              (pathRows package.verifier)
              (leafBoundF (ringChar package.FP) package.verifier.N package.verifier.claim) (2 ^ 110) := by
  intro hF hrowsC hmemC hmemW hleaf haxis
  obtain ⟨P, hS, hc⟩ :=
    nockCompiles_zmod (K := K) hrun hbound hs hf hK3 hq hF hrowsC hmemC hmemW hleaf haxis
  refine ⟨P, hS, hc, fun msg hst hV => ?_⟩
  exact (hS.standalone.soundness P.verifier hV msg hst).trans (hS.bound P.verifier _ _)

end

end Nock.NockVMROM.Thm54.TraceGen.VCL38

end Nock.Walk39
