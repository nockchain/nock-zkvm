/-
  Nock/RedTeam/Batch395Thm54SeedBoundaryDeployed.lean

  Paper re-read at source:
  * the paper — axis argument; `:1421` / `:1427` check accumulators at
    `halt` only and claim that "suffices"
  * the paper (`Algorithm:Memspec`) — `halt` zeros; `read_root` /
    `verify_child` relate parent/child; **no** start clause pinning root counts
  * the paper (`Corr:forest`) — seed over all `k` labelled roots

  Compiled scope already on the tree (re-checked, not re-proved):
  * `StrengtheningScope.lean::seed_counts_pins_the_axis`
  * `StrengtheningScope.lean::wrong_axis_satisfies_every_rowlocal_constraint`
  * `Nock/AIR.lean::memSeedBoundaryExprs` / `::memSeedBoundary_sound` (K-side only)

  Positive controls: the instrument finds `accInit` (first · role 43) and finds
  roles `3`/`4` read by `tab:v_mem`. K-side positive control:
  `memSeedBoundary_sound` rejects a nonzero root residual.
-/
import Nock.AIR
import Nock.MemoryTable
import Nock.ComputeTable
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.NockVMROM.Thm54.MixedCoordinateCompiler
import Nock.NockVMROM.Thm54.StrengtheningScope
import Nock.RedTeam.Batch272Thm54UnanchoredIntermediateEndpoints

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch395

open Nock
open Nock.Reified
open Nock.Reified.Trans
open Nock.MemoryTable
open Nock.ComputeTable (FP)
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.MemoryPaperFactorization hiding paperAggregator paperBaseGates
  paperKGates paperKGatesCore walkInitGates ioCoreGates tabVMemGates bottomPins accInit
  hostedWalkInitGates hostedWalkStepGates hostedWalkGates walkStepGates walkGates
open Nock.Thm54.StrengtheningScope
open Nock.RedTeam.Batch272


/-- Source roles of `pt.indicator` / `pt.counts` in the deployed `6/55` layout. -/
def axisAccumRoles : List ℕ := [3, 4]

def readsAxisAccumM {F : Type} (g : MixedExpr F) : Bool :=
  readsRoleM 3 g || readsRoleM 4 g

def readsAxisAccumC {F : Type} (g : CoeffExpr F) : Bool :=
  (leavesC g).any (fun v =>
    (v.1 == .traceCur || v.1 == .traceNext) && (v.2 == 3 || v.2 == 4))

/-- First-row mask on the deployed chip is base column `4` (`bcur 4`). A seed pin
of role `r` is a `Scale` of that mask times a leaf at role `r` (shape of `accInit`). -/
def isFirstRowScaleOfRole {F : Type} (r : ℕ) : MixedExpr F → Bool
  | .Scale mask body =>
      ((leavesC mask).any (fun v => decide (v = (.traceCur, 4)))) &&
        (leavesM body).any (fun v =>
          (v.1 == .traceCur || v.1 == .traceNext) && v.2 == r)
  | .Add x y | .Sub x y | .Mul x y =>
      isFirstRowScaleOfRole r x || isFirstRowScaleOfRole r y
  | .Neg x | .Pow x _ => isFirstRowScaleOfRole r x
  | .Var _ _ | .Lift _ | .Const _ => false

def isFirstRowAxisSeedPin {F : Type} (g : MixedExpr F) : Bool :=
  isFirstRowScaleOfRole 3 g || isFirstRowScaleOfRole 4 g

/-! ## Read-set census of the committed gate lists -/

/-- `walkAccInitInGate` is now
the mask-form `acc(1) = initial_count·cc(1)` and reads neither roles `3`/`4` nor a seed
public.  No committed gate has the first-row-`Scale`-of-roles-`3`/`4` shape. -/
theorem paperKGates_first_row_axis_shape :
    (paperKGates (F := ℚ) (K := ℚ)).map isFirstRowAxisSeedPin =
      [false, false, false, false, false, false, false, false, false, false,
       false, false, false, false, false, false, false, false, false, false,
       false, false, false, false, false, false, false, false, false, false,
       false, false, false, false, false, false, false, false, false, false,
       false, false, false, false, false, false, false, false, false] := by
  set_option maxRecDepth 100000 in decide

theorem hostedPaperKGates_no_first_row_axis_seed_pin :
    (Nock.NockVMROM.Thm54.MemoryPaperFactorization.hostedPaperKGates (F := ℚ) (K := ℚ) ).all
      (fun g => !isFirstRowAxisSeedPin g) = true := by
  set_option maxRecDepth 100000 in decide

/-- Reads the seed public. -/
def readsSeedPublic {F : Type} (g : MixedExpr F) : Bool :=
  (leavesM g).any (fun v => v.1 == .publicVal && v.2 == 1)

/-- In-gate seed: `walkAccInitInGate` reads `publicVal 0` (`initial_count`), not the seed public. -/
theorem walkAccInitInGate_reads_seed :
    readsSeedPublic (Nock.NockVMROM.Thm54.MemoryWalkLabel.walkAccInitInGate (F := ℚ) ) = false := by
  decide

/-- Positive control for the instrument's meaning: `accInit` (`first · role 43`) is a genuine
zero pin — it reads no public. -/
theorem accInit_reads_no_public : readsSeedPublic (accInit (F := ℚ) ) = false := by
  decide

/-- **No committed gate is a first-row zero pin of roles `3`/`4`**: the only flagged shape is the
seed comparison; a zero pin reads no public.  This is the finding's substance, unchanged. -/
theorem no_committed_zero_pin :
    (paperKGates (F := ℚ) (K := ℚ)).all (fun g => !isFirstRowAxisSeedPin g || readsSeedPublic g) = true := by
  set_option maxRecDepth 100000 in decide

/-- Base bucket: four state booleanities and the one-hot sum on base columns `0..3`. Axis accumulators live in **extension** roles `3`/`4` of
`paperKGates`, not in this base layout (base column `3` is a selector, not
`pt.indicator`). -/
theorem paperBaseGates_are_selector_booleanities :
    (paperBaseGates (F := ℚ) ).length = 5 := by
  decide

/-- The committed boundary gates: line, count, and mask-form acc init read no axis accumulator. -/
theorem walkInitGates_axis_reads :
    (walkInitGates (F := ℚ) ).map readsAxisAccumM = [false, false, false] := by
  decide

theorem hostedWalkInitGates_blind_to_axis_accumulators :
    (Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.hostedWalkInitGates (F := ℚ) ).all
      (fun g => !readsAxisAccumM g) = true := by
  decide

/-- The two intermediate endpoints stay blind; the authorized root-mask
    pair reads `pt.counts` / `pt.indicator` (roles `4` / `3`). -/
theorem paperEndpointGates_axis_reads :
    (paperEndpointGates (F := ℚ) ).map readsAxisAccumM =
      [false, false, true, true] := by
  decide

theorem ioCoreGates_blind_to_axis_accumulators :
    (ioCoreGates (F := ℚ) ).all (fun g => !readsAxisAccumM g) = true := by
  decide

/-- Positive control: existing first-row IO pin `accInit = first · role 43`. -/
theorem accInit_is_first_row_scale_of_role_43 :
    isFirstRowScaleOfRole (F := ℚ)  43 accInit = true := by
  decide

/-- Positive control: roles `3`/`4` are read by `tab:v_mem` (live columns; missing is a root pin). -/
theorem tabVMem_reads_axis_accumulators :
    (tabVMemGates (F := ℚ) (K := ℚ)).any readsAxisAccumM = true := by
  set_option maxRecDepth 100000 in decide

theorem bottomPins_not_first_row_axis_seed :
    (bottomPins (F := ℚ) (K := ℚ)).all (fun g => !isFirstRowAxisSeedPin g) = true := by
  decide

/-! ## StrengtheningScope bridge (V_mem / `eqBlk` only) -/

theorem seed_counts_pins_the_axis_reexport {K : Type*} [Field K]
    {inp : MemoryTable.Inputs K} {rRoot rDec rVC : MemoryTable.Pub K}
    (h2 : (2 : K) ≠ 0)
    (hRootSt : rRoot.st = .read_root) (hRoot : MemoryTable.eqBlk inp rRoot)
    (hDecSt : rDec.st = .decompose) (hDec : MemoryTable.eqBlk inp rDec)
    (hVCSt : rVC.st = .verify_child) (hVC : MemoryTable.eqBlk inp rVC)
    (edge1 : rRoot.lc = rDec.pt) (edge2 : rDec.rc = rVC.pt)
    (haltL : rDec.lc.indicator = 0 ∧ rDec.lc.counts = 0)
    (haltV : rVC.lc.indicator = 0 ∧ rVC.lc.counts = 0)
    (hts : rVC.mem.ts = rRoot.mem.ts) (ht : rRoot.mem.ts ≠ 0)
    (hlamR : rRoot.lambda? = some 1) (hlamD : rDec.lambda? = some 1)
    (hlamV : rVC.lambda? = some 1)
    (hC : rRoot.cprime? = none) :
    rRoot.pt.indicator = rRoot.mem.ts * (1 - rRoot.mem.axis)
      ∧ rRoot.pt.counts = rRoot.mem.ts * (2 - rRoot.mem.axis) :=
  seed_counts_pins_the_axis h2 hRootSt hRoot hDecSt hDec hVCSt hVC
    edge1 edge2 haltL haltV hts ht hlamR hlamD hlamV hC

theorem wrong_axis_satisfies_every_rowlocal_constraint_reexport {K : Type*} [Field K]
    {inp : MemoryTable.Inputs K} (h2 : (2 : K) ≠ 0) (a t : K)
    (nL nR : FP K) (hL : AtomShape inp.z nL) (hR : AtomShape inp.z nR) :
    ∃ rRoot rDec rVC rHL rHR : MemoryTable.Pub K,
      rRoot.st = .read_root ∧ MemoryTable.eqBlk inp rRoot ∧
      rDec.st = .decompose ∧ MemoryTable.eqBlk inp rDec ∧
      rVC.st = .verify_child ∧ MemoryTable.eqBlk inp rVC ∧
      rHL.st = .halt ∧ MemoryTable.eqBlk inp rHL ∧
      rHR.st = .halt ∧ MemoryTable.eqBlk inp rHR ∧
      rRoot.lc = rDec.pt ∧ rDec.lc = rHL.pt ∧ rDec.rc = rVC.pt ∧ rVC.lc = rHR.pt ∧
      rVC.mem.axis = a ∧ rVC.mem.ts = t ∧ rRoot.mem.ts = t ∧
      rRoot.pt.counts = t :=
  wrong_axis_satisfies_every_rowlocal_constraint h2 a t nL nR hL hR

/-- Concrete instance over `ℚ`: axis `5`, `t = 1`; residual forces `counts_root ≠ 0`. -/
theorem wrong_axis_five_over_rat :
    ∃ (inp : MemoryTable.Inputs ℚ) (rRoot rVC : MemoryTable.Pub ℚ),
      rRoot.st = .read_root ∧ MemoryTable.eqBlk inp rRoot ∧
      rVC.st = .verify_child ∧ MemoryTable.eqBlk inp rVC ∧
      rVC.mem.axis = (5 : ℚ) ∧ rRoot.mem.ts = (1 : ℚ) ∧
      rRoot.pt.counts = (1 : ℚ) ∧ rRoot.pt.counts ≠ 0 := by
  let inp : MemoryTable.Inputs ℚ := { z := 2, γ := 0, β := 0 }
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have hL : AtomShape (2 : ℚ) (FP.atomFP (2 : ℚ) 0) := atomFP_atomShape _ _
  have hR : AtomShape (2 : ℚ) (FP.atomFP (2 : ℚ) 1) := atomFP_atomShape _ _
  obtain ⟨rRoot, _, rVC, _, _, hStR, hEqR, _, _, hStV, hEqV, _, _, _, _, _, _, _, _,
      hAxis, _, htsR, hRes⟩ :=
    wrong_axis_satisfies_every_rowlocal_constraint  (inp := inp) h2
      (5 : ℚ) (1 : ℚ) (FP.atomFP 2 0) (FP.atomFP 2 1) hL hR
  refine ⟨inp, rRoot, rVC, hStR, hEqR, hStV, hEqV, hAxis, htsR, hRes, ?_⟩
  intro hc
  rw [hc] at hRes
  norm_num at hRes

/-! ## K-side positive control (`memoryAIRchained`) -/

theorem memSeed_in_memoryAIRchained :
    (⟨.boundary, memSeedCountsExpr⟩ : Constraint) ∈ (memoryAIRchained (K := ℚ)).constraints ∧
      (⟨.boundary, memSeedIndicatorExpr⟩ : Constraint) ∈ (memoryAIRchained (K := ℚ)).constraints :=
  ⟨memSeedCounts_mem_memoryAIRchained (K := ℚ), memSeedIndicator_mem_memoryAIRchained (K := ℚ)⟩

theorem memSeedBoundary_sound_reexport
    {K : Type*} [Field K]
    (minp : MemoryTable.Inputs K) (mop : MemoryTable.MState → K) (mrow : MemoryTable.Pub K)
    (mg : K) :
    (∀ e ∈ memSeedBoundaryExprs, e.eval (Reified.memoryEnvFull minp mop mrow mg) = 0)
      ↔ (mrow.pt.counts = 0 ∧ mrow.pt.indicator = 0) :=
  memSeedBoundary_sound minp mop mrow mg

theorem k_side_rejects_nonzero_root_counts {K : Type*} [Field K]
    (minp : MemoryTable.Inputs K) (mop : MemoryTable.MState → K) (mrow : MemoryTable.Pub K)
    (mg : K) (h : mrow.pt.counts ≠ 0) :
    ¬ (∀ e ∈ memSeedBoundaryExprs, e.eval (Reified.memoryEnvFull minp mop mrow mg) = 0) := by
  intro hall
  exact h ((memSeedBoundary_sound minp mop mrow mg).1 hall).1

/-! ## Consumed chip vs K-side -/

theorem paperKGates_length_is_45 :
    (paperKGates (F := ℚ) (K := ℚ)).length = 49 :=
  paperKGates_length

theorem consumed_first_row_pins_exist :
    isFirstRowScaleOfRole (F := ℚ)  43 accInit = true ∧
      (walkInitGates (F := ℚ) ).length = 3 := by
  constructor <;> decide

/-- **FINDING (gate-set, LU-class).**  Deployed memory chip commits no first-row
axis-accumulator ZERO pin; `tab:v_mem` reads roles `3`/`4` only through row-local
recurrences and halt zeros; walk / IO / intermediate first-row pins are other
roles; K-side `memSeedBoundaryExprs` absent from `paperKGates`. Paper `:1427`
"this suffices" is a paper gap closed on the K-side AIR only. -/
theorem finding_deployed_memory_chip_misses_axis_seed_boundary :
    (paperKGates (F := ℚ) (K := ℚ)).all (fun g => !isFirstRowAxisSeedPin g || readsSeedPublic g) = true ∧
      (Nock.NockVMROM.Thm54.MemoryPaperFactorization.hostedPaperKGates (F := ℚ) (K := ℚ) ).all
        (fun g => !isFirstRowAxisSeedPin g) = true ∧
      (paperBaseGates (F := ℚ) ).length = 5 ∧
      (walkInitGates (F := ℚ) ).map readsAxisAccumM = [false, false, false] ∧
      (paperEndpointGates (F := ℚ) ).map readsAxisAccumM =
        [false, false, true, true] ∧
      (ioCoreGates (F := ℚ) ).all (fun g => !readsAxisAccumM g) = true ∧
      (tabVMemGates (F := ℚ) (K := ℚ)).any readsAxisAccumM = true ∧
      isFirstRowScaleOfRole (F := ℚ)  43 accInit = true :=
  ⟨no_committed_zero_pin, hostedPaperKGates_no_first_row_axis_seed_pin,
    paperBaseGates_are_selector_booleanities, walkInitGates_axis_reads,
    paperEndpointGates_axis_reads,
    ioCoreGates_blind_to_axis_accumulators, tabVMem_reads_axis_accumulators,
    accInit_is_first_row_scale_of_role_43⟩

#print axioms finding_deployed_memory_chip_misses_axis_seed_boundary
#print axioms memSeed_in_memoryAIRchained
#print axioms k_side_rejects_nonzero_root_counts
#print axioms wrong_axis_five_over_rat

end Nock.RedTeam.Batch395
