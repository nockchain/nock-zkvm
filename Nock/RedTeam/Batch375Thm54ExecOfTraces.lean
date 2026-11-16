/-
  Nock/RedTeam/Batch375Thm54ExecOfTraces.lean

  **`cfgOfTraces` / `execOfTraces` and the defining
  equation as a theorem.**

  `execOfTraces_computePubAt_eq_decodePub` is a **proved lemma**, not a
  structure field and not a hypothesis:

      (execOfTraces P Qc Qm c h).computePubAt i
        = decodePub (rowEnvAt P c (familyQc P c Qc) (Fin.cast … i))
            (lblC P Qc c (i.val + 1)).1

  It follows from `Walk.reconTree_labels` plus the
  definition of `lblC`.  Walk-tiling `TracesWalkHyps` is carried
  (`hSf` / `hvalid`); close from deployed walk gates in step 5.

  `strategyOfTraces : ProductionStrategy` is **not** inhabited (step 3).
-/
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.NockVMROM.Thm54.FamilyComputeRows
import Nock.NockVMROM.Thm54.ChainedLanguage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch375

open scoped Polynomial
open Polynomial
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator

abbrev computePubAt_eq_decodePub
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (i : Fin (cfgOfTraces P Qc Qm c).compRows) :
    (execOfTraces P Qc Qm c h).computePubAt i =
      decodePub
        (rowEnvAt P c (familyQc P c Qc)
          (Fin.cast (cfgOfTraces_compRows P Qc Qm c) i))
        (lblC P Qc c (i.val + 1)).1 :=
  execOfTraces_computePubAt_eq_decodePub P Qc Qm c h i

/-- Twin for `Dec`. -/
abbrev computeDecAt_eq_decodeDec
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (i : Fin (cfgOfTraces P Qc Qm c).compRows) :
    (execOfTraces P Qc Qm c h).computeDecAt i =
      decodeDec
        (rowEnvAt P c (familyQc P c Qc)
          (Fin.cast (cfgOfTraces_compRows P Qc Qm c) i)) :=
  execOfTraces_computeDecAt_eq_decodeDec P Qc Qm c h i

/-- Twin for memory `Pub`. -/
abbrev memoryPubAt_eq_decodeMemPub
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (i : Fin (cfgOfTraces P Qc Qm c).memRows) :
    (execOfTraces P Qc Qm c h).memoryPubAt i =
      decodeMemPub P Qm c (Fin.cast (cfgOfTraces_memRows P Qc Qm c) i) :=
  execOfTraces_memoryPubAt_eq_decodeMemPub P Qc Qm c h i

/-- `cfgOfTraces.compRows` is the `Qc` label-list length. -/
theorem cfgOfTraces_compRows_is_Qc_list
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    (cfgOfTraces P Qc Qm c).compRows = (computeLabelList P Qc c).length :=
  rfl

/-- `cfgOfTraces.memRows` is the `Qm` label-list length. -/
theorem cfgOfTraces_memRows_is_Qm_list
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    (cfgOfTraces P Qc Qm c).memRows = (memoryLabelList P Qm c).length :=
  rfl

#check execOfTraces_computePubAt_eq_decodePub
#check computePubAt_eq_decodePub

end Nock.RedTeam.Batch375

#print axioms Nock.RedTeam.Batch375.computePubAt_eq_decodePub
#print axioms Nock.RedTeam.Batch375.computeDecAt_eq_decodeDec
#print axioms Nock.RedTeam.Batch375.memoryPubAt_eq_decodeMemPub
#print axioms Nock.RedTeam.Batch375.cfgOfTraces_compRows_is_Qc_list
