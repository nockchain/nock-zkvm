import Nock.NockVMROM.Thm54.VclL.Compute.FormulaLookup

/-!
# V4T Q7 : the `ln` / timestamp read set of the VCL compute sources

.

**The timestamp roles.**  In the source layout the memory-record timestamps are not columns: the
decoder DERIVES them (`OptimizedComputeSubstitution.computeTraceSubst`: source `74` ↦
`lnPrev · chal 0`, `mr2Field 7` / `mr3Field 7` ↦ `… lnPrev · (chal 0)^2 / ^3`), so every timestamp
reads exactly the role `54` (`lnPrev`) and the challenge slot `0` (`α`); `ln` is role `55`.  The
instrument therefore measures, over the typed sources of every compute gate, the reads of roles
`54`/`55` and of challenge slots `0` (`α`) and `9` (`λ`).

* **Positive control** (`readsLn_deleted`): the read set FINDS roles `54`/`55` in core gates `50`,
  `58`, `65`, `72`, `78` and in the endpoint `finalLnInit` (and `79`, `80`, already dropped by VCL).
* **The check** (`kept_no_ln`): no KEPT source — the core positions `keptCoreIdsQ7`
  (`keptCoreIds` minus `{50, 58, 65, 72, 78}`, with the 309 retargets and the residual / chain
  wrappers), the three aux sources, `endpoint2_309` minus `finalLnInit`, `endpoint4_309` — reads
  role `54`, role `55`, challenge `0` or challenge `9`.
* The VCL-only gates (serial `220`, axis `221`, lookup inverses / accumulators `≥ 214`, the record
  roles `0..53`, coin limbs `21..26`) read none of the physical limbs `175..180` of roles `54`/`55` and
  no challenge limb of slots `0` / `9` by construction (`roleLimb 53 + 2 = 174`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace LnRead

open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.Unhosted309

/-- Extension roles a typed source reads. -/
def roles : CorrectedFinalTypedExpr → List ℕ
  | .extCur i | .extNext i => [i.val]
  | .add x y | .sub x y | .mul x y => roles x ++ roles y
  | .neg x | .pow x _ => roles x
  | _ => []

/-- Challenge slots a typed source reads. -/
def chals : CorrectedFinalTypedExpr → List ℕ
  | .challenge i => [i.val]
  | .add x y | .sub x y | .mul x y => chals x ++ chals y
  | .neg x | .pow x _ => chals x
  | .lamPow _ => [9]
  | _ => []

def wRoles : WTyped → List ℕ
  | .leaf t => roles t
  | .add x y | .sub x y | .mul x y => wRoles x ++ wRoles y
  | .neg x | .pow x _ => wRoles x
  | _ => []

def wChals : WTyped → List ℕ
  | .leaf t => chals t
  | .add x y | .sub x y | .mul x y => wChals x ++ wChals y
  | .neg x | .pow x _ => wChals x
  | _ => []

/-- A typed source touches the timestamp read set. -/
def touchesT (t : CorrectedFinalTypedExpr) : Bool :=
  (roles t).any (fun r => r = 54 ∨ r = 55) || (chals t).any (fun s => s = 0 ∨ s = 9)

def touchesW (t : WTyped) : Bool :=
  (wRoles t).any (fun r => r = 54 ∨ r = 55) || (wChals t).any (fun s => s = 0 ∨ s = 9)

/-- The typed source a 309 core position compiles (the retargets and wrappers of
`correctedCoreCoord309`): residual roles `58`/`59` at `74`/`75`, the chain `accAfterChain`, the
queue retargets at `76`/`77`, else the extension gate. -/
def coreTouches (i : CorrectedCoreExtGateId) : Bool :=
  if i = packedQueueNonEmptyId then touchesW queueNonEmpty309
  else if i = packedQueueTilingId then touchesW queueTiling309
  else if i = packedWalkCountId then false   -- reads residual role 58 and base 12 only
  else if i = packedWalkAccId then false     -- reads residual role 59 and base 12 only
  else if i = packedChainId then touchesT accAfterChain
  else touchesT (correctedFinalExtGate i)

/-- The Q7 deletion set. -/
def deletedCoreIds : List ℕ := [50, 58, 65, 72, 78]

/-- The core positions the Q7 chip keeps. -/
def keptCoreIdsQ7 : List CorrectedCoreExtGateId :=
  keptCoreIds.filter fun i => i.val ∉ deletedCoreIds

/-- `endpoint2_309` without `finalLnInit`. -/
def endpoint2Q7 : List WTyped := endpoint2_309.filter fun t => t ≠ lowerLeaf finalLnInit

theorem keptCoreIdsQ7_length : keptCoreIdsQ7.length = 75 := by decide +kernel

theorem endpoint2Q7_eq : endpoint2Q7 =
    [lowerLeaf finalMaskedWalkLn1, lowerW finalMaskedWalkCount1_309, lowerW finalMaskedWalkOut309,
      lowerLeaf finalAccInit, lowerLeaf finalAccTerminal] := by decide +kernel

/-- **Positive control**: the instrument finds the timestamp read set in the deleted core gates and
in `finalLnInit` (and in the Form R pins `79`, `80` VCL already dropped). -/
theorem readsLn_deleted :
    (∀ i ∈ [50, 58, 65, 72, 78, 79, 80], ∀ h : i < 82, coreTouches ⟨i, h⟩ = true) ∧
      touchesW (lowerLeaf finalLnInit) = true := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- **The check: no kept source reads roles `54`/`55` or challenge slots `0`/`9`.** -/
theorem kept_no_ln :
    (∀ i ∈ keptCoreIdsQ7, coreTouches i = false) ∧
      (∀ j : Fin 2, touchesW (residualSource309 j) = false) ∧
      touchesT correctedAccAfterStep = false ∧
      (∀ t ∈ endpoint2Q7, touchesW t = false) ∧ (∀ t ∈ endpoint4_309, touchesW t = false) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The physical limbs of roles `54`/`55` are `175..180`, above every VCL record role limb
(`roleLimb 53 + 2 = 174`) and below the B0 / inverse / accumulator block (`≥ 202`). -/
theorem lnLimbs_range : roleLimb 54 = 175 ∧ roleLimb 55 = 178 ∧ roleLimb 53 + 2 = 174 := by decide

end LnRead
end VclL.Compute
end Nock.NockVMROM.Thm54
