import Nock.RedTeam.Batch1964Thm54VclCompletenessChosen
import Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

/-!
* `hrowsC` OUT (no VSQ consumer: the honest datum does not need it, `V.Checks` is a premise of the hostile bound);
* `hs`, `hf` are consumed by the honest-acceptance conjunct (`pkgOfRun_accepted`, `hat_of_run`).

`∃ package, Statement package ∧ claim ∧
(∀ χ, HonestGoodVSQ … χ → AcceptsG package.verifier (honest message) χ)`; `nockCompilesHostile` adds the
staged bound over EVERY verifier datum `V'` with `V'.Checks` (any claim, in particular a false one), not only
at the package's own (true-claim) verifier.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen.VCL38

open _root_.Nock _root_.Nock.Walk _root_.Nock.NockVMROM.Thm54 _root_.Nock.NockVMROM.Thm54.SVFrame _root_.Nock.NockVMROM.Thm54.SVFrameG
open _root_.Nock.NockVMROM.Thm54.T0Tower _root_.Nock.NockVMROM.Thm54.TraceGen
open _root_.Nock.NockVMROM.Thm54.VclL _root_.Nock.NockVMROM.Thm54.VclL.Chips _root_.Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open _root_.Nock.NockVMROM.Thm54.VclL.Compute _root_.Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open _root_.Nock.NockVMROM.Thm54.VclL.Compute.TowerChosen _root_.Nock.NockVMROM.Thm54.VclL.Events
open _root_.Nock.NockVMROM.Thm54.VclL.GenWalk
open _root_.Nock.NockVMROM.Thm54.VclL.Handle _root_.Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open _root_.Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ _root_.Nock.NockVMROM.Thm54.VclL.Handle.PullVSQ
open _root_.Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ _root_.Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS
open Nock.NockVMROM.Thm54.VclL.Handle.CoresVSQH
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage

noncomputable section

attribute [local instance] ringCharFactW algZModW decQ40

/-! ## 1. -/

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

theorem δc_nonsquare {K : Type} [Field K] [Algebra F K] [Fintype K]
    (hq : 2 ^ 63 < ringChar F) (hK3 : Module.finrank F K = 3) :
    ¬ IsSquare (algebraMap F K (δc hq)) :=
  T0Tower.nonsquare_lift (F := F) (K := K) (two_ne_of_hq hq)
    (by rw [← Algebra.ringChar_eq F K]; exact two_ne_of_hq hq) hK3 _ (δc_spec hq).1 (δc_spec hq).2

end Delta

/-! ## 2. The package built from the run -/

section Heights
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  {fuel : ℕ} {subject formula result : Noun}
  (hrun : Nock.evalN fuel subject formula = some result)
  (hbound : RunBoundedBy (ringChar F) fuel subject formula)

/-- The generator accepts the run's tree (`romTree_spec`). -/
theorem genR : genComputeSkeleton (K := Quad (algebraMap F K δF)) fuel subject formula =
    .ok (runTree (K := K) δF hrun hbound, result) :=
  romTree_spec _

/-- **The VSQ package built from the run** at the chosen heights. -/
def pkgOfRun [CharP K (ringChar K)] (hK3 : Module.finrank F K = 3) (hq : 2 ^ 63 < ringChar F)
    (hFprime : GeneratedField.PrimeFieldElems F)
    (hF : 3 * 2 ^ (max (hCq (runTree (K := K) δF hrun hbound))
        (max (hTq (runTree (K := K) δF hrun hbound)) (hPq (runTree (K := K) δF hrun hbound)))) ∣
          Fintype.card F - 1)
    (hmemC : (demandH2 (runRowsH (runTree (K := K) δF hrun hbound))).cells.length + 1 < ringChar F)
    (hmemW : krW (demandH2 (runRowsH (runTree (K := K) δF hrun hbound))).cells
        (demandH2 (runRowsH (runTree (K := K) δF hrun hbound))).preads +
      (walkRows (demandH2 (runRowsH (runTree (K := K) δF hrun hbound))).cells
        (demandH2 (runRowsH (runTree (K := K) δF hrun hbound))).preads).length < ringChar F)
    (hleaf : programLeafBound (airReorder (runTree (K := K) δF hrun hbound)) ≤ 2 ^ 109)
    (haxis : programAxisBound (airReorder (runTree (K := K) δF hrun hbound)) < 2 ^ 63)
    (hop5 : programOp5DepthOK (runTree (K := K) δF hrun hbound)) :
    OptimizedFullStrictNockVMROMPackage F K (hCq (runTree (K := K) δF hrun hbound)) where
  δ := δF
  hT := hTq (runTree (K := K) δF hrun hbound)
  hP := hPq (runTree (K := K) δF hrun hbound)
  kr := krW (demandH2 (runRowsH (runTree (K := K) δF hrun hbound))).cells
    (demandH2 (runRowsH (runTree (K := K) δF hrun hbound))).preads
  honest := hVS_of_run (δF := δF) (genR δF hrun hbound)
    (vsVerifierOfRun hrun (genR δF hrun hbound) hK3 hF) hFprime hq (fun _ _ => rfl)
    (vsV_hsizeM hrun (genR δF hrun hbound) hK3 hF) (vsV_hC0 hrun (genR δF hrun hbound) hK3 hF)
    (vsV_hW0 hrun (genR δF hrun hbound) hK3 hF) (B := 2 ^ 109) hleaf (by norm_num) haxis hop5 hmemC hmemW
  t := runTree (K := K) δF hrun hbound
  x := xOfRun (t := runTree (K := K) δF hrun hbound) (subject := subject) (formula := formula) (result := result)
  fuel := fuel
  hgen := genR δF hrun hbound
  hd := rfl
  hm := claimMsgOf_full _ _
  hN := rfl

/-- A message at the `Honest := Empty` VSQ cores, read at the honest-carrying cores (same fields). -/
def ofE {hT hP kr hC : ℕ}
    (msg : MessagesG (compCoreVSQ δF hT hP hC (sumCVSQ (F := F) (K := K) hT hP hC))
      (memCoreVSQ δF hT hP kr hC (sumMVSQ (F := F) (K := K) δF hT hP kr hC))) :
    MessagesG (compCoreVSQH (K := K) δF hT hP kr hC) (memCoreVSQH (K := K) δF hT hP kr hC) where
  Qc := msg.Qc
  Qm := msg.Qm
  msg0C := msg.msg0C
  msg0M := msg.msg0M
  requests := msg.requests
  msg2M := msg.msg2M

/-- **Honest acceptance at the package built from the run**: at every coin where the honest-acceptance premise
`HonestGoodVSQ` holds (the event whose failure the `completeness` field prices), the honest messages are
accepted by the package's verifier at the statement's cores. -/
theorem pkgOfRun_accepted [CharP K (ringChar K)] (hK3 : Module.finrank F K = 3) (hq : 2 ^ 63 < ringChar F)
    (hFprime : GeneratedField.PrimeFieldElems F)
    (hs : FieldEmbedding.BoundedBy (ringChar F) subject) (hf : FieldEmbedding.BoundedBy (ringChar F) formula)
    (hF : 3 * 2 ^ (max (hCq (runTree (K := K) δF hrun hbound))
        (max (hTq (runTree (K := K) δF hrun hbound)) (hPq (runTree (K := K) δF hrun hbound)))) ∣
          Fintype.card F - 1)
    (hmemC : (demandH2 (runRowsH (runTree (K := K) δF hrun hbound))).cells.length + 1 < ringChar F)
    (hmemW : krW (demandH2 (runRowsH (runTree (K := K) δF hrun hbound))).cells
        (demandH2 (runRowsH (runTree (K := K) δF hrun hbound))).preads +
      (walkRows (demandH2 (runRowsH (runTree (K := K) δF hrun hbound))).cells
        (demandH2 (runRowsH (runTree (K := K) δF hrun hbound))).preads).length < ringChar F)
    (hleaf : programLeafBound (airReorder (runTree (K := K) δF hrun hbound)) ≤ 2 ^ 109)
    (haxis : programAxisBound (airReorder (runTree (K := K) δF hrun hbound)) < 2 ^ 63)
    (hop5 : programOp5DepthOK (runTree (K := K) δF hrun hbound))
    (χ : Coins frameVSQ K)
    (hχ : HonestGoodVSQ (pkgOfRun δF hrun hbound hK3 hq hFprime hF hmemC hmemW hleaf haxis hop5).honest
      (pkgOfRun δF hrun hbound hK3 hq hFprime hF hmemC hmemW hleaf haxis hop5).t
      (pkgOfRun δF hrun hbound hK3 hq hFprime hF hmemC hmemW hleaf haxis hop5).x χ) :
    AcceptsG (pkgOfRun δF hrun hbound hK3 hq hFprime hF hmemC hmemW hleaf haxis hop5).verifier
      (ofE δF (msgD δF _ _ _ _ (pkgOfRun δF hrun hbound hK3 hq hFprime hF hmemC hmemW hleaf haxis hop5).hdat))
      χ := by
  have h := honest_accepted_VSQ_whp
    (sumC := sumCVSQ (F := F) (K := K) (hTq (runTree (K := K) δF hrun hbound))
      (hPq (runTree (K := K) δF hrun hbound)) (hCq (runTree (K := K) δF hrun hbound)))
    (sumM := sumMVSQ (F := F) (K := K) δF (hTq (runTree (K := K) δF hrun hbound))
      (hPq (runTree (K := K) δF hrun hbound))
      (krW (demandH2 (runRowsH (runTree (K := K) δF hrun hbound))).cells
        (demandH2 (runRowsH (runTree (K := K) δF hrun hbound))).preads)
      (hCq (runTree (K := K) δF hrun hbound)))
    (pkgOfRun δF hrun hbound hK3 hq hFprime hF hmemC hmemW hleaf haxis hop5).honest
    (pkgOfRun δF hrun hbound hK3 hq hFprime hF hmemC hmemW hleaf haxis hop5).t
    (pkgOfRun δF hrun hbound hK3 hq hFprime hF hmemC hmemW hleaf haxis hop5).x
    (genR δF hrun hbound) rfl (claimMsgOf_full _ _) rfl
    (vsV_injC hrun (genR δF hrun hbound) hK3 hF) (vsV_adjC hrun (genR δF hrun hbound) hK3 hF)
    (hroot_of_run (genR δF hrun hbound)) (hbs_of_run (genR δF hrun hbound)) (hslot_of_run (genR δF hrun hbound))
    (hat_of_run (by have := hq; omega) hrun hbound hs hf (genR δF hrun hbound)) χ hχ
  exact ⟨h.compute, h.memory⟩

end Heights

/-! ## 3. `nockCompiles_p76` (general `F`) -/

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
    ∀ (hF : 3 * 2 ^ (max (hCq (runTree (K := K) (δc hq) hrun hbound))
        (max (hTq (runTree (K := K) (δc hq) hrun hbound)) (hPq (runTree (K := K) (δc hq) hrun hbound)))) ∣
          Fintype.card F - 1)
      (hmemC : (demandH2 (runRowsH (runTree (K := K) (δc hq) hrun hbound))).cells.length + 1 < ringChar F)
      (hmemW : krW (demandH2 (runRowsH (runTree (K := K) (δc hq) hrun hbound))).cells
          (demandH2 (runRowsH (runTree (K := K) (δc hq) hrun hbound))).preads +
        (walkRows (demandH2 (runRowsH (runTree (K := K) (δc hq) hrun hbound))).cells
          (demandH2 (runRowsH (runTree (K := K) (δc hq) hrun hbound))).preads).length < ringChar F)
      (hleaf : programLeafBound (airReorder (runTree (K := K) (δc hq) hrun hbound)) ≤ 2 ^ 109)
      (haxis : programAxisBound (airReorder (runTree (K := K) (δc hq) hrun hbound)) < 2 ^ 63)
      (hop5 : programOp5DepthOK (runTree (K := K) (δc hq) hrun hbound)),
    ∃ package : OptimizedFullStrictNockVMROMPackage F K (hCq (runTree (K := K) (δc hq) hrun hbound)),
      OptimizedFullStrictThm54Statement package ∧
        package.honest.V.claim = ⟨subject, formula, result⟩ ∧
        ∀ χ : Coins frameVSQ K, HonestGoodVSQ package.honest package.t package.x χ →
          AcceptsG package.verifier (ofE package.δ (msgD package.δ _ _ _ _ package.hdat)) χ := by
  intro hF hmemC hmemW hleaf haxis hop5
  haveI : Fact (¬ IsSquare (algebraMap F K (δc hq))) := ⟨δc_nonsquare hq hK3⟩
  exact ⟨pkgOfRun (K := K) (δc hq) hrun hbound hK3 hq hFprime hF hmemC hmemW hleaf haxis hop5,
    optimizedFullStrictNockVMROM_of_package _, rfl,
    pkgOfRun_accepted (K := K) (δc hq) hrun hbound hK3 hq hFprime hs hf hF hmemC hmemW hleaf haxis hop5⟩

/-! ## 4. `nockCompiles_zmod` (`F = ZMod p`) -/

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
    ∀ (hF : 3 * 2 ^ (max (hCq (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound)))
        (max (hTq (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound)))
          (hPq (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))))) ∣ p - 1)
      (hmemC : (demandH2 (runRowsH (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound)))).cells.length + 1 < p)
      (hmemW : krW (demandH2 (runRowsH (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound)))).cells
          (demandH2 (runRowsH (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound)))).preads +
        (walkRows (demandH2 (runRowsH (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound)))).cells
          (demandH2 (runRowsH (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound)))).preads).length < p)
      (hleaf : programLeafBound (airReorder (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))) ≤ 2 ^ 109)
      (haxis : programAxisBound (airReorder (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))) < 2 ^ 63)
      (hop5 : programOp5DepthOK (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))),
    ∃ package : OptimizedFullStrictNockVMROMPackage (ZMod p) K
        (hCq (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))),
      OptimizedFullStrictThm54Statement package ∧
        package.honest.V.claim = ⟨subject, formula, result⟩ ∧
        ∀ χ : Coins frameVSQ K, HonestGoodVSQ package.honest package.t package.x χ →
          AcceptsG package.verifier (ofE package.δ (msgD package.δ _ _ _ _ package.hdat)) χ := by
  intro hF hmemC hmemW hleaf haxis hop5
  have hr : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hs' : FieldEmbedding.BoundedBy (ringChar (ZMod p)) subject := by rw [hr]; exact hs
  have hf' : FieldEmbedding.BoundedBy (ringChar (ZMod p)) formula := by rw [hr]; exact hf
  have hF' := hF
  rw [show p - 1 = Fintype.card (ZMod p) - 1 by rw [ZMod.card]] at hF'
  exact nockCompiles_p76 (F := ZMod p) (K := K) hrun (hbz hbound) hs' hf' hK3 (hqz hq)
    (GeneratedField.primeFieldElems_zmod p) hF' (by rw [hr]; exact hmemC) (by rw [hr]; exact hmemW)
    hleaf haxis hop5

/-! ## 5. `nockCompilesHostile`: the staged bound at the compiler-built verifier -/

open Classical in
theorem nockCompilesHostile {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    [FiniteDimensional (ZMod p) K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    {fuel : ℕ} {subject formula result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy p fuel subject formula)
    (hs : FieldEmbedding.BoundedBy p subject) (hf : FieldEmbedding.BoundedBy p formula)
    (hK3 : Module.finrank (ZMod p) K = 3) (hq : 2 ^ 63 < p) :
    haveI : Fact (¬ IsSquare (algebraMap (ZMod p) K (δc (hqz hq)))) := ⟨δc_nonsquare (hqz hq) hK3⟩
    ∀ (hF : 3 * 2 ^ (max (hCq (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound)))
        (max (hTq (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound)))
          (hPq (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))))) ∣ p - 1)
      (hmemC : (demandH2 (runRowsH (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound)))).cells.length + 1 < p)
      (hmemW : krW (demandH2 (runRowsH (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound)))).cells
          (demandH2 (runRowsH (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound)))).preads +
        (walkRows (demandH2 (runRowsH (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound)))).cells
          (demandH2 (runRowsH (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound)))).preads).length < p)
      (hleaf : programLeafBound (airReorder (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))) ≤ 2 ^ 109)
      (haxis : programAxisBound (airReorder (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))) < 2 ^ 63)
      (hop5 : programOp5DepthOK (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))),
    ∃ package : OptimizedFullStrictNockVMROMPackage (ZMod p) K
        (hCq (runTree (K := K) (δc (hqz hq)) hrun (hbz hbound))),
      OptimizedFullStrictThm54Statement package ∧
        package.honest.V.claim = ⟨subject, formula, result⟩ ∧
        (∀ χ : Coins frameVSQ K, HonestGoodVSQ package.honest package.t package.x χ →
          AcceptsG package.verifier (ofE package.δ (msgD package.δ _ _ _ _ package.hdat)) χ) ∧
        ∀ (V' : VerifierData (ZMod p) K _ package.shape) (msg : MessagesG package.CF package.MF),
          TracesStaged frameVSQ (tableVSQ _) package.shape msg.traces →
          V'.Checks (fun a => package.CF.reqBound V' a + package.MF.internalBound V' a) (ringChar package.FP) →
          ((Finset.univ.filter fun χ : Coins frameVSQ K =>
              AcceptsG V' msg χ ∧ ¬ SVGenuineF.HoldsF (ringChar K) V'.claim).card : ℚ) /
              Fintype.card (Coins frameVSQ K) ≤
            boundVCLHQ'' (Fintype.card K) (Fintype.card package.FP) V'.N
              (V'.memRows (tCQ package.hT package.hP)) (V'.memRows (tWQ package.hT package.hP))
              (claimFuel V'.claim) := by
  intro hF hmemC hmemW hleaf haxis hop5
  obtain ⟨P, hS, hc, hacc⟩ :=
    nockCompiles_zmod (K := K) hrun hbound hs hf hK3 hq hF hmemC hmemW hleaf haxis hop5
  refine ⟨P, hS, hc, hacc, fun V' msg hst hV => ?_⟩
  exact (hS.standalone.soundness V' hV msg hst).trans (hS.bound V' _ _)

end

end Nock.NockVMROM.Thm54.TraceGen.VCL38

