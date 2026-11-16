/-
  Nock/NockVMROM/Thm54/WrapFixesVcomp.lean

  The relative wrap is the identity on a
  `V_comp` row.  Landed form: identity,
  not the `↔` weakening.
-/
import Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.NockVMROM.Thm54.FamilyComputeRows
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.Framework.NockInstances
import Nock.NockVMROM.Thm54.P8Core.WrapFixesVcomp
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.WrapFixesVcomp

open scoped Polynomial
open Polynomial
open Nock
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.Reified
open Nock.Framework
open MonolithicRAP

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

/-- `memBlk` pins `ln = ln_prev · α^{recordCount}`. -/
theorem memBlk_ln (inp : Inputs K) (pub : Pub K) (dec : Dec K)
    (h : memBlk inp pub dec) :
    pub.ln = pub.ln_prev * inp.α ^ Nock.Framework.recordCount pub.state := by
  cases hst : pub.state <;> simp_all [memBlk, Nock.Framework.recordCount]

/-- Always-on record 1. -/
theorem Vcomp.mr1_eq {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (h : Vcomp inp pub dec) :
    pub.mr1 = ⟨pub.f, dec.f_t, 3, pub.ln_prev * inp.α⟩ :=
  h.2.1

theorem Vcomp.memBlk {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (h : Vcomp inp pub dec) :
    memBlk inp pub dec :=
  h.2.2.2.1

/-- Active `mr2.ts` is `ln_prev · α²`; inactive `mr2` is zero (`memBlk`). -/
theorem memBlk_mr2 (inp : Inputs K) (pub : Pub K) (dec : Dec K)
    (h : memBlk inp pub dec) :
    (Nock.Framework.recordCount pub.state ≤ 1 → pub.mr2 = MemRec.zero) ∧
      (1 < Nock.Framework.recordCount pub.state →
        pub.mr2.ts = pub.ln_prev * inp.α ^ 2) := by
  cases hst : pub.state <;> simp_all [memBlk, Nock.Framework.recordCount]

/-- Active `mr3.ts` is `ln_prev · α³`; inactive `mr3` is zero (`memBlk`). -/
theorem memBlk_mr3 (inp : Inputs K) (pub : Pub K) (dec : Dec K)
    (h : memBlk inp pub dec) :
    (Nock.Framework.recordCount pub.state ≤ 2 → pub.mr3 = MemRec.zero) ∧
      (2 < Nock.Framework.recordCount pub.state →
        pub.mr3.ts = pub.ln_prev * inp.α ^ 3) := by
  cases hst : pub.state <;> simp_all [memBlk, Nock.Framework.recordCount]

theorem inputs_eq_of_alpha (inp : Inputs K) {α : K} (h : inp.α = α) :
    ({ inp with α := α } : Inputs K) = inp := by
  cases inp
  cases h
  rfl

/-- **Fixed-point of the relative wrap on a `V_comp` row.**  `recordCount` is `memBlk`'s arity. -/
theorem wrap_fixes_vcomp_row
    (st : State) (inp : Inputs K) (pub : Pub K) (dec : Dec K) (α : K)
    (hα : inp.α = α)
    (hst : st = pub.state)
    (hv : Vcomp inp pub dec) :
    (wrapComputeLabel (st, (inp, pub, dec))).specialize α =
      (st, (inp, pub, dec)) := by
  have hblk := Vcomp.memBlk hv
  have hln := memBlk_ln inp pub dec hblk
  have hmr1 := Vcomp.mr1_eq hv
  have hmr2 := memBlk_mr2 inp pub dec hblk
  have hmr3 := memBlk_mr3 inp pub dec hblk
  have hinp := inputs_eq_of_alpha inp hα
  have horigin :
      computeLineOrigin inp.α pub.ln_prev 0 * α ^ 0 = pub.ln_prev := by
    simp [computeLineOrigin]
  have hln' :
      pub.ln_prev * α ^ (Nock.Framework.recordCount st - 0) = pub.ln := by
    rw [Nat.sub_zero, hst, ← hα, hln]
  have hpos : 0 < Nock.Framework.recordCount st :=
    Nat.succ_le_iff.mp (Nock.Framework.recordCount_pos st)
  have hmr1' :
      specializeMemRecScaled α pub.ln_prev
          (decide (computeMemRecKind st (0 : Fin 3) = .active))
          ((0 : Fin 3).val + 1 - 0) pub.mr1 = pub.mr1 := by
    have hact : computeMemRecKind st (0 : Fin 3) = .active := by
      simp [computeMemRecKind, hpos]
    simp only [specializeMemRecScaled, hact, decide_true, if_true]
    refine MemRec.ext rfl rfl rfl ?_
    have hts : pub.mr1.ts = pub.ln_prev * α := by
      simp [hmr1, hα]
    simpa using hts.symm
  have hmr2' :
      specializeMemRecScaled α pub.ln_prev
          (decide (computeMemRecKind st (1 : Fin 3) = .active))
          ((1 : Fin 3).val + 1 - 0) pub.mr2 = pub.mr2 := by
    by_cases hk : computeMemRecKind st (1 : Fin 3) = .active
    · have hgt : 1 < Nock.Framework.recordCount st := by
        simpa [computeMemRecKind] using hk
      have hts := hmr2.2 (by simpa [hst] using hgt)
      simp only [specializeMemRecScaled, hk, decide_true, if_true]
      refine MemRec.ext rfl rfl rfl ?_
      simpa [hα] using hts.symm
    · have hle : Nock.Framework.recordCount st ≤ 1 := by
        have : ¬ (1 : ℕ) < Nock.Framework.recordCount st := by
          simpa [computeMemRecKind] using hk
        exact Nat.not_lt.mp this
      have hz := hmr2.1 (by simpa [hst] using hle)
      simp only [specializeMemRecScaled, hk, decide_false]
      exact hz.symm
  have hmr3' :
      specializeMemRecScaled α pub.ln_prev
          (decide (computeMemRecKind st (2 : Fin 3) = .active))
          ((2 : Fin 3).val + 1 - 0) pub.mr3 = pub.mr3 := by
    by_cases hk : computeMemRecKind st (2 : Fin 3) = .active
    · have hgt : 2 < Nock.Framework.recordCount st := by
        simpa [computeMemRecKind] using hk
      have hts := hmr3.2 (by simpa [hst] using hgt)
      simp only [specializeMemRecScaled, hk, decide_true, if_true]
      refine MemRec.ext rfl rfl rfl ?_
      simpa [hα] using hts.symm
    · have hle : Nock.Framework.recordCount st ≤ 2 := by
        have : ¬ (2 : ℕ) < Nock.Framework.recordCount st := by
          simpa [computeMemRecKind] using hk
        exact Nat.not_lt.mp this
      have hz := hmr3.1 (by simpa [hst] using hle)
      simp only [specializeMemRecScaled, hk, decide_false]
      exact hz.symm
  unfold wrapComputeLabel ComputeRowTemplate.specialize
  simp only []
  rw [horigin, hinp, hmr1', hmr2', hmr3', hln']
  cases pub
  cases hst
  rfl

noncomputable section

variable {F : Type} [Field F] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Decoded label state agrees with the one-hot witness of `VcompAt`. -/
theorem lblCAt_state_eq
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    (lblCAt P Qc c i).1 =
      (decodePub (rowEnvAt P c (familyQc P c Qc) i)
        (lblCAt P Qc c i).1).state := by
  simp [lblCAt, decodePub, pubOfState]

private theorem getElem_map_range'_one {α : Type*} (f : ℕ → α) {n i : ℕ}
    (hi : i < n) :
    ((List.range' 1 n).map f)[i]'(by simp [List.length_map, List.length_range']; exact hi) =
      f (i + 1) := by
  rw [List.getElem_map, List.getElem_range']
  simp [Nat.add_comm]

/-- **Corollary.**  On an accepted family row the specialized public is the
decoded public (`wrap_fixes_vcomp_row`). -/
theorem specializedExec_computePubAt_eq_decodePub_of_accepted
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0)
    (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc))
    (i : Fin ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).compRows) :
    ((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computePubAt i =
      decodePub
        (rowEnvAt P c (familyQc P c Qc)
          (Fin.cast
            ((specializedExec_compRows P Qc Qm c h hz).trans
              (cfgOfTraces_compRows P Qc Qm c)) i))
        (lblCAt P Qc c
          (Fin.cast
            ((specializedExec_compRows P Qc Qm c h hz).trans
              (cfgOfTraces_compRows P Qc Qm c)) i)).1 := by
  have hcfg := specializedExec_compRows P Qc Qm c h hz
  have hN := cfgOfTraces_compRows P Qc Qm c
  have hi : (i : ℕ) < P.optimized.family.problem.cfg.compRows := by omega
  have hi' : (i : ℕ) < (cfgOfTraces P Qc Qm c).compRows := by omega
  have hv := deployed_row_vcomp_at P c (familyQc P c Qc) hsat hz ⟨i.val, hi⟩
  have hV := lblCAt_vcomp_of_vcompAt P Qc c ⟨i.val, hi⟩ hv
  have hα : (lblCAt P Qc c ⟨i.val, hi⟩).2.1.α = alphaM c.1 := by
    have := decodeInputs_eq_specialized P Qc c ⟨i.val, hi⟩
    simpa [lblCAt] using congrArg Inputs.α this
  have hst : (lblCAt P Qc c ⟨i.val, hi⟩).1 =
      (lblCAt P Qc c ⟨i.val, hi⟩).2.2.1.state := by
    simp [lblCAt, decodePub, pubOfState]
  have hfix :=
    wrap_fixes_vcomp_row
      (lblCAt P Qc c ⟨i.val, hi⟩).1
      (lblCAt P Qc c ⟨i.val, hi⟩).2.1
      (lblCAt P Qc c ⟨i.val, hi⟩).2.2.1
      (lblCAt P Qc c ⟨i.val, hi⟩).2.2.2
      (alphaM c.1) hα hst (by simpa [lblCAt] using hV)
  have hmap := specialized_computeRows_map P Qc Qm c h hz
  have hexec := execOfTraces_computeRows P Qc Qm c h
  have hlenE : (execOfTraces P Qc Qm c h).computeRows.length =
      (cfgOfTraces P Qc Qm c).compRows :=
    (execOfTraces P Qc Qm c h).computeRows_length
  have hidxE : (i : ℕ) < (execOfTraces P Qc Qm c h).computeRows.length := by
    omega
  have hget :
      (execOfTraces P Qc Qm c h).computeRows[(i : ℕ)]'hidxE =
        lblCAt P Qc c ⟨i.val, hi⟩ := by
    rw [List.getElem_of_eq hexec, getElem_map_range'_one (lblC P Qc c) hi']
    exact lblC_succ P Qc c ⟨i.val, hi⟩
  have hlenS :
      ((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeRows.length =
        (execOfTraces P Qc Qm c h).computeRows.length := by
    rw [hmap, List.length_map]
  have hidxS : (i : ℕ) <
      ((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeRows.length := by
    omega
  have hrow :
      ((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeRows[(i : ℕ)]'hidxS =
        (wrapComputeLabel (lblCAt P Qc c ⟨i.val, hi⟩)).specialize (alphaM c.1) := by
    simp only [hmap]
    rw [List.getElem_map]
    exact congrArg (fun row => (wrapComputeLabel row).specialize (alphaM c.1)) hget
  have hpub :
      ((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computePubAt i =
        (((strategyOfTraces P Qc Qm c h).specializedExec
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeRows[(i : ℕ)]'hidxS).2.2.1 := by
    unfold ExactExecution.computePubAt ExactExecution.computeRowAt
    rw [List.get_eq_getElem]
    congr 1
  have hcast :
      Fin.cast
        ((specializedExec_compRows P Qc Qm c h hz).trans
          (cfgOfTraces_compRows P Qc Qm c)) i =
        ⟨i.val, hi⟩ :=
    Fin.ext rfl
  rw [hpub, hrow, hfix, hcast]
  simp [lblCAt]

end

end Nock.NockVMROM.Thm54.WrapFixesVcomp
