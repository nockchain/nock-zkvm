import Nock.NockVMROM.Thm54.OptimizedMemoryRAP
import Nock.NockVMROM.Thm54.PaperResourceCounts
import Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
import Nock.AIR

/-!

Nothing here is a new statement about
the memory language; every declaration is a *count* or a *syntactic identification* that the prose
document cites, so that the document's arithmetic is machine-checked rather than asserted.

* `App:Memconstraints` is the paper (the next `\section` is the paper).  Its five
  named blocks are **Label Variables** (`:2092`), **Memory Record Accesses** (`:2115`, typing
  `:2117`), **Intermediate Aggregator** (`:2120`, identity `:2123`; `:2119` is blank),
  **State Variables** (`:2126`, booleanity `:2130`, one-hot `:2131`) and **Equality Constraints**
  (`:2134`, `Table tab:v_mem` `:2136-2171`).  `decompose`/`halt`/`read_root`/`verify_child` are the
  four *columns* of that table, not blocks of the section.
* `Algorithm:Memspec` is the paper; its per-state clauses are `:2057-2060` (decompose),
  `:2062-2064` (halt), `:2066-2072` (read_root), `:2074-2080` (verify_child).
* Theorem 5.4's memory resource list is the paper: `61·e+13` columns (`:1479`),
  `24·e+16` degree-`4` transition gates (`:1483`), `2·e` degree-`1` (`:1487`), `2·e` degree-`3`
  (`:1488`), four equality checks (`:1489`).

1. The two cut out the same solution set at any one-hot
   selector (`MemoryFactorizationScope.mergedMemCore_iff_perStateGated`,
   `MemoryFactorizationScope.lean:366`), so this is a regrouping, not a change of language.
2.
3. `decompressed_equality_checks_overshoot` / `decompressed_transition_overshoots_at_e_one` — the
   de-compressed shape (three scalar compressions expanded to `3` gates each, the selector
   compression to `12` checks) cannot meet the paper's numbers.
4. `compressionCoin_index_below_baseCols` — the four base-field compression coins occupy challenge
   indices `0,1,2,3`, strictly below the chip's `baseCols = 6`, hence disjoint from every
   coordinate of every extension challenge.
5. `degreeOneEndpoints_are_intermediate_endpoints` and `degreeThreeEndpoint_is_walk_terminal` —
   the paper's two `intermediate` endpoint gates and the walk terminal
   `out_walk = 0` are in the tree, in the endpoint buckets, *not* in the
   four equality checks.  **Since the `LU` repair all four sit in the degree-`≤ 3`
   bucket and the degree-`1` bucket is empty**: the `intermediate` gates are the paper's
   `first · ipre`/`last · icur` (degree `2`), where previously they were the product-column
   pins `46 = 0`, `49 = 0` that `Nock/RedTeam/Batch272…` showed bound nothing.
6. `selectorEquality_vanishes_on_mirror_binding` — the four things the tree *does* call equality
   checks enforce nothing but agreement between an extension-valued state-selector mirror
   (ext roles `51..54`) and the base-field selector column.  No paper constraint says this.
-/

namespace Nock.NockVMROM.Thm54
namespace GateCorrespondenceMemory

open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryCoreInventory
open Module
open CoordinateCompiler
open CoordinateBasis
open MonolithicRAP

/-! ## 1. The row-local transcription census (`Nock/AIR.lean:1748`) -/

/-- Per-state equality-block sizes of the `tab:v_mem` transcription
(`Nock/AIR.lean:1530`, paper the paper). -/
theorem memEqBlkExprs_lengths :
    (Reified.memEqBlkExprs (K := ℚ) MemoryTable.MState.decompose).length = 13 ∧
      (Reified.memEqBlkExprs (K := ℚ) MemoryTable.MState.halt).length = 22 ∧
      (Reified.memEqBlkExprs (K := ℚ) MemoryTable.MState.read_root).length = 14 ∧
      (Reified.memEqBlkExprs (K := ℚ) MemoryTable.MState.verify_child).length = 14 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Per-state `intermediate` block sizes (`Nock/AIR.lean:1560`, paper the paper). -/
theorem memInterExprs_lengths :
    (Reified.memInterExprs MemoryTable.MState.decompose).length = 1 ∧
      (Reified.memInterExprs MemoryTable.MState.halt).length = 1 ∧
      (Reified.memInterExprs MemoryTable.MState.read_root).length = 2 ∧
      (Reified.memInterExprs MemoryTable.MState.verify_child).length = 2 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The State-Variables block: four booleanities plus one one-hot sum. -/
theorem memSvExprs_length : Reified.memSvExprs.length = 5 := rfl

/-- The whole row-local memory AIR: `5` State-Variables gates, `1` `z·zinv = 1` witness gate
, and `69` selector-gated
per-state gates. -/
theorem memoryAIR_census :
    Reified.memoryAIR (K := ℚ).constraints.length = 75 ∧
      Reified.memPerStateGated (K := ℚ).length = 69 := by
  refine ⟨rfl, rfl⟩

/-! ### 1b.

`Nock.Reified.memoryAIR` above is the *transcription* and is unchanged.  What the chip compiles is
`OptimizedMemoryGateBasis.memoryRowSources`, and that now carries the merged core. -/

/-- **The merged source census.**  `5` State-Variables gates, the `z · zinv = 1` witness, and the
`27` selector-summed quantity classes: `33` row-local sources, `50` semantic sources in all, `40`
of them in the extension fold — against `75 / 92 / 82` before the merge. -/
theorem mergedMemorySource_census :
    OptimizedMemoryGateBasis.memoryRowSources (K := ℚ).length = 33 ∧
      OptimizedMemoryGateBasis.mergedMemoryCore (K := ℚ).length = 27 ∧
      OptimizedMemoryGateBasis.transitionSources (K := ℚ).length = 50 ∧
      OptimizedMemoryGateBasis.extensionFoldSources (K := ℚ).length = 40 := by
  refine ⟨OptimizedMemoryGateBasis.memoryRowSources_length,
    OptimizedMemoryGateBasis.mergedMemoryCore_length, by decide, by decide⟩

/-- **The three list lengths behind the `69 → 27` regrouping.**  This is a *count*, not an
equivalence: it says the per-state list has `69` entries and both merged cores have `27`.  The
statement that the two cut out the same solution set is elsewhere and is two theorems —
`MemoryFactorizationScope.mergedMemCore_iff_perStateGated` (`:366`) in the forward-and-backward
direction *under an assumed one-hot selector*, and
`MergedSourceBridge.merged_sources_recover_memoryAIR`, which derives the selector from the
shipped sources under `(2 : K) ≠ 0`. -/
theorem merge_ratio : Reified.memPerStateGated (K := ℚ).length = 69 ∧
    OptimizedMemoryGateBasis.mergedMemoryCore (K := ℚ).length = 27 ∧
    (MemoryFactorizationScope.mergedMemCore (K := ℚ)).length = 27 :=
  ⟨rfl, OptimizedMemoryGateBasis.mergedMemoryCore_length,
    MemoryFactorizationScope.mergedMemCore_length⟩

/-- **The fold's per-row bad-challenge price falls `61 → 19`.**  Each bucket now folds two
sources instead of four, so nineteen buckets contribute one root each and two contribute none. -/
theorem merged_fold_workload :
    (OptimizedMemoryCollisionAccounting.extensionFoldFamilies.map
      fun es => es.length - 1).sum = 19 :=
  OptimizedMemoryCollisionAccounting.extensionFoldFamilies_workload

/-- **No gate numeral moved — by the Option-B memory-core merge.**  At the merge the template
still carried `14` base and `21` extension transition gates.  That is a statement about the
merge; the later `𝔽 → 𝕂` retyping does move those two counts, to `11` and `24`,
and moves the memory chip's `s` to `112` through `RAPPadding.memoryFinalTotalConstraintsMixed`;
A-mem-2 moves it to `113` and the deployed transition
bucket to `89` (`Thm54Resources.memoryTransitionGates`).  The numerals below are the
pre-retyping definitions and the paper's own formula (`Thm54Resources.memoryTransitionGatesPaper`),
which are unchanged and still true; they are *not* the deployed chip's current counts. -/
theorem merge_moves_no_gate_numeral :
    RAPPadding.memoryCoreTransitionGates 3 = 77 ∧
      RAPPadding.memoryFinalTotalConstraints 3 = 104 ∧
      Thm54Resources.memoryColumns 3 = 205 ∧
      Thm54Resources.memoryTransitionGatesPaper 3 = 88 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The forest-walk gadget as exported: three boundary, three transition and
one terminal gate. -/
theorem walkAIR_census : Reified.Trans.walkAIR.constraints.length = 7 := rfl

/-- The chained memory AIR adds the cross-row `intermediate` hand-off, the two axis seed
boundaries and the two LogUp endpoint pins. -/
theorem memoryAIRchained_census :
    Reified.Trans.memoryAIRchained (K := ℚ).constraints.length = 80 := rfl

/-- The memory-IO accumulator gadget as exported. -/
theorem ioMemAIR_census : Reified.Trans.ioMemAIR.constraints.length = 3 := rfl

/-! ## 2. The transition budget: `88 = 77 semantic + 11 inert`

`OptimizedMemoryGateBasis.memorySourceTemplate` (`:1096`) carries `14` base-field and `21`
extension-valued transition gates, so the coordinate-expanded semantic count is `14 + 21·e`.
Theorem 5.4 asks for `24·e+16`.  The difference is exactly
`RAPPadding.residualTransitionGates e = 3·e+2`, and `RAPPadding.padMemoryCore_residual_compose_zero`
(`RAPPadding.lean:395`) proves each appended residual gate composes to the zero polynomial. -/

/-- Semantic (non-residual) memory transition gates, coordinate-expanded. -/
def semanticTransitionGates (e : ℕ) : ℕ := 14 + 21 * e

theorem semanticTransitionGates_deployed : semanticTransitionGates 3 = 77 := rfl

/-- **The `24·e+16` match is padding-completed, not gate-for-gate.** -/
theorem memory_transition_budget (e : ℕ) :
    semanticTransitionGates e + RAPPadding.residualTransitionGates e =
      Thm54Resources.memoryTransitionGatesPaper e := by
  simp only [semanticTransitionGates, RAPPadding.residualTransitionGates,
    Thm54Resources.memoryTransitionGatesPaper]
  omega

theorem memory_transition_budget_deployed :
    semanticTransitionGates 3 = 77 ∧
      RAPPadding.residualTransitionGates 3 = 11 ∧
      Thm54Resources.memoryTransitionGatesPaper 3 = 88 := by
  refine ⟨rfl, rfl, rfl⟩

/-- The residual bucket is a free parameter: *any* semantic core at or below `24·e+16` can be
padded to it.  The only non-trivial fact the match carries is that the same residual `3·e+2`
closes both chips, i.e. that the two semantic cores differ by exactly `1`, as the paper's
`24·e+15` / `24·e+16` do. -/
theorem residual_closes_both_chips (e : ℕ) :
    RAPPadding.computeCoreTransitionGates e + RAPPadding.residualTransitionGates e =
        Thm54Resources.computeTransitionGatesPaper e ∧
      RAPPadding.memoryCoreTransitionGates e + RAPPadding.residualTransitionGates e =
        Thm54Resources.memoryTransitionGatesPaper e ∧
      RAPPadding.memoryCoreTransitionGates e = RAPPadding.computeCoreTransitionGates e + 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [RAPPadding.computeCoreTransitionGates, RAPPadding.memoryCoreTransitionGates,
      RAPPadding.residualTransitionGates, Thm54Resources.computeTransitionGatesPaper,
      Thm54Resources.memoryTransitionGatesPaper] <;>
    omega

/-- The tree's semantic core is exactly `RAPPadding.memoryCoreTransitionGates`. -/
theorem semanticTransitionGates_eq_core (e : ℕ) :
    semanticTransitionGates e = RAPPadding.memoryCoreTransitionGates e := by
  simp only [semanticTransitionGates, RAPPadding.memoryCoreTransitionGates]
  omega

/-! ### 2b. The paper's own decomposition of `24·e+16`, with zero slack

Theorem 5.4's memory transition budget is the sum of three *named* paper objects, and the sum is
exact:

* `Thm:mem_38`: `RAP_mem` alone is `54·e+5` columns and `20·e+13` degree-`4`
  transition gates.
* `Thm:Walk_IOP` transition constraints: `2 + 2·e` gates of degree `1`,
  `s_F` gates for `F` (which is `RAP_mem`, already counted), and `e` gates of degree `3`.
* `Thm:IO_result` `RAP_mem-IO` additional transition costs: one gate of
  degree `1` and `e` gates of degree `3`; plus `e+1` columns.

The same three objects also close the column count `61·e+13`, leaving the walk's
own column share as the remainder.  Both identities below are the paper's arithmetic, not the
tree's. -/

/-- `RAP_mem` transition gates, the paper. -/
def paperVmemTransitionGates (e : ℕ) : ℕ := 20 * e + 13

/-- Walk-gadget transition gates, the paper (`2 + 2·e` of degree `1`) and the paper
(`e` of degree `3`). -/
def paperWalkTransitionGates (e : ℕ) : ℕ := (2 + 2 * e) + e

/-- `RAP_mem-IO` additional transition gates, the paper (one of degree `1`) and
the paper (`e` of degree `3`). -/
def paperMemIOTransitionGates (e : ℕ) : ℕ := 1 + e

/-- `RAP_mem` columns, the paper. -/
def paperVmemColumns (e : ℕ) : ℕ := 54 * e + 5

/-- `RAP_mem-IO` additional columns, the paper. -/
def paperMemIOColumns (e : ℕ) : ℕ := e + 1

/-- **Theorem 5.4's `24·e+16` is exactly the sum of its three named pieces.** -/
theorem paper_memory_transition_decomposes (e : ℕ) :
    paperVmemTransitionGates e + paperWalkTransitionGates e + paperMemIOTransitionGates e
      = Thm54Resources.memoryTransitionGatesPaper e := by
  simp only [paperVmemTransitionGates, paperWalkTransitionGates, paperMemIOTransitionGates,
    Thm54Resources.memoryTransitionGatesPaper]
  omega

/-- **The tree's semantic core is numerically `V_mem` plus `RAP_mem-IO`.** -/
theorem tree_core_equals_vmem_plus_memIO (e : ℕ) :
    RAPPadding.memoryCoreTransitionGates e
      = paperVmemTransitionGates e + paperMemIOTransitionGates e := by
  simp only [RAPPadding.memoryCoreTransitionGates, paperVmemTransitionGates,
    paperMemIOTransitionGates]
  omega

/-- **The tree's `3·e+2` residual is numerically the walk gadget's whole transition budget.**
It is only *numerically* so: `extensionFoldSources` already contains `walkBoundarySources` and
`walkTransitionSources`, and the gates actually appended by the padding compose to the zero
polynomial (`RAPPadding.padMemoryCore_residual_compose_zero`). -/
theorem tree_residual_equals_paper_walk (e : ℕ) :
    RAPPadding.residualTransitionGates e = paperWalkTransitionGates e := by
  simp only [RAPPadding.residualTransitionGates, paperWalkTransitionGates]
  omega

/-- The same three objects close the column count `61·e+13`, plus, since the
29th, the one round-0 pre-seed `atom` column (`OptimizedMemoryGateBasis.atomCol`) and, since the
31st, the round-0 exponent carrier `reqIdx` (`OptimizedMemoryGateBasis.reqIdxCol`; the trailing
`+ 1 + 1`). -/
theorem paper_memory_columns_decompose (e : ℕ) :
    paperVmemColumns e + paperMemIOColumns e + e + e + e + RAPPadding.memoryResidualColumns e + 1
      + 1 = Thm54Resources.memoryColumns e := by
  simp only [paperVmemColumns, paperMemIOColumns, RAPPadding.memoryResidualColumns,
    Thm54Resources.memoryColumns]
  omega

theorem tree_core_columns_equal_vmem_plus_memIO (e : ℕ) :
    RAPPadding.memoryCoreWidth e = paperVmemColumns e + paperMemIOColumns e + e + e + e := by
  simp only [RAPPadding.memoryCoreWidth, paperVmemColumns, paperMemIOColumns]
  omega

/-! ### 2c. The gate deficit is exactly the residual

Read affinely, Theorem 5.4 asks for `24` `𝕂`-valued and `16` base-field transition gates
; the tree's `memorySourceTemplate` supplies `21` and `14`
(`OptimizedMemoryGateBasis.lean:1112-1119`).  The shortfall `3·e + 2` is, coefficient for
coefficient, `RAPPadding.residualTransitionGates`. -/

def paperExtensionTransitionGates : ℕ := 24
def paperBaseTransitionGates : ℕ := 16
def treeExtensionTransitionGates : ℕ := 21
def treeBaseTransitionGates : ℕ := 14

theorem paper_transition_affine (e : ℕ) :
    paperExtensionTransitionGates * e + paperBaseTransitionGates
      = Thm54Resources.memoryTransitionGatesPaper e := by
  simp only [paperExtensionTransitionGates, paperBaseTransitionGates,
    Thm54Resources.memoryTransitionGatesPaper]

theorem tree_transition_affine (e : ℕ) :
    treeExtensionTransitionGates * e + treeBaseTransitionGates = semanticTransitionGates e := by
  simp only [treeExtensionTransitionGates, treeBaseTransitionGates, semanticTransitionGates]
  omega

/-- **The residual is the deficit, coefficient for coefficient.** -/
theorem deficit_equals_residual (e : ℕ) :
    (paperExtensionTransitionGates - treeExtensionTransitionGates) * e
        + (paperBaseTransitionGates - treeBaseTransitionGates)
      = RAPPadding.residualTransitionGates e := by
  simp only [paperExtensionTransitionGates, treeExtensionTransitionGates,
    paperBaseTransitionGates, treeBaseTransitionGates, RAPPadding.residualTransitionGates]

/-! ## 3. De-compression is arithmetically excluded

Expanding the three scalar base compressions (`firstMaskBindingGate` `:875`,
`lastMaskBindingGate` `:879`, `intermediateChainGate` `:887`) into their three coordinates each
turns `14` base transition gates into `20`; expanding `selectorEquality` (`:1039`) turns the four
equality checks into twelve. -/

def decompressedBaseTransition : ℕ := 20
def decompressedEqualityChecks : ℕ := 12
def decompressedTransitionGates (e : ℕ) : ℕ := decompressedBaseTransition + 21 * e

/-- `12 ≠ 4`: equality
checks are not padded, so de-compression could never reach the tree's four. W2 stage 2: live `memoryEqualityChecks = 0`; de-compression still
costs `12`. Previously a `12 = 4·e` form. -/
theorem decompressed_equality_checks_meets_retyped_count :
    decompressedEqualityChecks = 12 ∧
      Thm54Resources.memoryEqualityChecks Thm54Resources.deployedExtensionDegree = 0 := by
  decide

/-- At `e = 1` the de-compressed semantic core already exceeds the paper's **entire** memory
transition budget, so no non-negative residual can close it: `41 > 40`. -/
theorem decompressed_transition_overshoots_at_e_one :
    Thm54Resources.memoryTransitionGatesPaper 1 < decompressedTransitionGates 1 := by decide

/-- The compressed core, by contrast, fits under `24·e+16` for every `e`. -/
theorem compressed_transition_fits (e : ℕ) :
    semanticTransitionGates e ≤ Thm54Resources.memoryTransitionGatesPaper e := by
  simp only [semanticTransitionGates, Thm54Resources.memoryTransitionGatesPaper]
  omega

/-! ## 4. The four base-field compression coins

`selectorEqualityChallenge`/`firstMaskBindingChallenge`/`lastMaskBindingChallenge`/
`chainBindingChallenge` (`OptimizedMemoryGateBasis.lean:862-865`) are base-field challenge
columns `0,1,2,3`.  The chip's `baseCols` is `6`, and coordinate expansion lays the `e`
coordinates of extension challenge `idx` at base indices `6 + e·idx … 6 + e·idx + (e-1)`
(`CoordinateRAPCore.lean:272`), so the coins alias nothing.  Note the paper samples **only**
`𝕂`-elements — one for the memory chip — so these four have no paper counterpart
as coins. -/

def compressionCoinIndices : List ℕ := [0, 1, 2, 3]

theorem memorySourceTemplate_baseCols {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (b : Basis (Fin 3) F K) :
    (memorySourceTemplate b).baseCols = 6 := by
  simp [memorySourceTemplate, ChipTemplate.baseCols] <;> rfl

/-- No compression-coin index is a coordinate of any extension challenge. -/
theorem compressionCoin_index_below_baseCols {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (b : Basis (Fin 3) F K)
    (i : ℕ) (hi : i ∈ compressionCoinIndices) (idx k : ℕ) (hk : k < 3) :
    i ≠ (memorySourceTemplate b).col0 3 VarKind.challenge idx + k := by
  have hb : (memorySourceTemplate b).baseCols = 6 := memorySourceTemplate_baseCols b
  have hi4 : i < 4 := by
    simp only [compressionCoinIndices, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> omega
  simp only [ChipTemplate.col0, hb]
  omega

/-- The three scalar compressions and the selector compression read four *distinct* coins. -/
theorem compressionCoins_distinct {F : Type} [Field F] :
    (selectorEqualityChallenge (F := F) = CoeffExpr.var VarKind.challenge 0) ∧
      (firstMaskBindingChallenge (F := F) = CoeffExpr.var VarKind.challenge 1) ∧
      (lastMaskBindingChallenge (F := F) = CoeffExpr.var VarKind.challenge 2) ∧
      (chainBindingChallenge (F := F) = CoeffExpr.var VarKind.challenge 3) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 5. Where the paper's boundary equalities actually live

`sampledMemoryRoleValue` (`OptimizedMemorySemanticRealization.lean:82`) fixes the sampled roles:
index `10` (= extension role `47`) is the first-row mask, index `11` (= role `48`) the last-row
mask, table roles `27`/`28` are `ipre`/`icur`, and forest-walk role `33` is the walk accumulator
column. **Since the `LU` repair** the two `intermediate` endpoint gates are the
paper's `first · ipre` and `last · icur` themselves, written over the mask
mirrors — `OptimizedMemoryGateBasis.intermediateInitGate = role 47 · role 27`,
`intermediateTerminalGate = role 48 · role 28` — and, being degree `2`, sit in the degree-`≤ 3`
bucket beside the walk endpoints, so `degreeOneEndpoints` is empty. The second degree-`3` endpoint gate is the walk terminal
`out_walk = 0`. -/

theorem degreeOneEndpoints_are_intermediate_endpoints :
    degreeOneEndpoints = [] ∧
      intermediateInitGate =
        Expr.Mul (Expr.Var VarKind.traceCur 47) (Expr.Var VarKind.traceCur 27) ∧
      intermediateTerminalGate =
        Expr.Mul (Expr.Var VarKind.traceCur 48) (Expr.Var VarKind.traceCur 28) ∧
      intermediateInitGate ∈ foldedDegreeThreeEndpoints ∧
      intermediateTerminalGate ∈ foldedDegreeThreeEndpoints :=
  ⟨rfl, rfl, rfl, intermediateInitGate_mem, intermediateTerminalGate_mem⟩

theorem degreeThreeEndpoint_is_walk_terminal :
    foldedDegreeThreeEndpoints =
      [Expr.Var VarKind.traceCur 41,
        Expr.Mul (Expr.Var VarKind.traceCur 48) (Expr.Var VarKind.traceCur 33),
        intermediateInitGate, intermediateTerminalGate] := rfl

/-- The tree's cross-row `intermediate` hand-off gate, the one thing the `chain` coin compresses
(`Nock/AIR.lean:1937`; paper-implicit at the paper, where one witness row carries both
`intermediate_i` and `intermediate_{i+1}`). -/
theorem chainCoord_is_masked_icur_handoff {F : Type} [Field F] (k : Fin 3) :
    chainCoord (F := F) k =
      CoeffExpr.mul (CoeffExpr.sub (CoeffExpr.const 1) (CoeffExpr.var VarKind.traceCur 5))
        (CoeffExpr.sub (CoeffExpr.var VarKind.traceCur (6 + 3 * 28 + (k : ℕ)))
          (CoeffExpr.var VarKind.traceNext (6 + 3 * 27 + (k : ℕ)))) := rfl

/-! ## 6. What the four "equality checks" actually enforce

`equalityChecks b = List.ofFn (selectorEquality b)` (`OptimizedMemoryGateBasis.lean:1046`), and
`selectorEquality b s` (`:1039`) is a random linear combination, in the base coin `challenge 0`, of
the three coordinate differences between extension role `51 + s` (the state-selector *mirror*,
`OptimizedMemoryCoreInventory.lean:60-63`) and base column `s` (the state selector itself).  It
therefore vanishes on any row where the mirror is the image of the selector — which is a fact about
the tree's base/extension column split, not about `V_mem`. -/

theorem selectorEquality_vanishes_on_mirror_binding
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (s : Fin 4) (env : Env F)
    (h : ∀ (k : ℕ) (hk : k < 3),
        env.trace (6 + 3 * (51 + (s : ℕ)) + k)
          = coord b (1 : K) ⟨k, hk⟩ * env.trace (s : ℕ)) :
    (selectorEquality b s).eval env = 0 := by
  simp only [selectorEquality, CoeffExpr.sumList, List.finRange, List.ofFn, Fin.foldr,
    Fin.foldr.loop, CoeffExpr.eval, List.foldr_cons, List.foldr_nil]
  linear_combination h 0 (by omega) +
    (selectorEqualityChallenge (F := F)).eval env * h 1 (by omega) +
    ((selectorEqualityChallenge (F := F)).eval env) ^ 2 * h 2 (by omega)

/-- The four equality checks read only the mirror block `51..54` and the base selector block
`0..3`; in particular none of them reaches the `intermediate` roles `27,28` or the memory-record
roles `19..26`. -/
theorem equalityChecks_read_only_mirror_and_selector (s : Fin 4) :
    6 + 3 * (51 + (s : ℕ)) ≥ 159 ∧ (s : ℕ) < 4 := by
  refine ⟨by omega, s.isLt⟩

end GateCorrespondenceMemory
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.GateCorrespondenceMemory.memoryAIR_census
#print axioms Nock.NockVMROM.Thm54.GateCorrespondenceMemory.mergedMemorySource_census
#print axioms Nock.NockVMROM.Thm54.GateCorrespondenceMemory.merged_fold_workload
#print axioms Nock.NockVMROM.Thm54.GateCorrespondenceMemory.merge_moves_no_gate_numeral
#print axioms Nock.NockVMROM.Thm54.GateCorrespondenceMemory.memory_transition_budget
#print axioms Nock.NockVMROM.Thm54.GateCorrespondenceMemory.paper_memory_transition_decomposes
#print axioms Nock.NockVMROM.Thm54.GateCorrespondenceMemory.tree_core_equals_vmem_plus_memIO
#print axioms Nock.NockVMROM.Thm54.GateCorrespondenceMemory.tree_residual_equals_paper_walk
#print axioms Nock.NockVMROM.Thm54.GateCorrespondenceMemory.paper_memory_columns_decompose
#print axioms Nock.NockVMROM.Thm54.GateCorrespondenceMemory.deficit_equals_residual
#print axioms Nock.NockVMROM.Thm54.GateCorrespondenceMemory.decompressed_equality_checks_meets_retyped_count
#print axioms Nock.NockVMROM.Thm54.GateCorrespondenceMemory.decompressed_transition_overshoots_at_e_one
#print axioms Nock.NockVMROM.Thm54.GateCorrespondenceMemory.compressionCoin_index_below_baseCols
#print axioms Nock.NockVMROM.Thm54.GateCorrespondenceMemory.degreeOneEndpoints_are_intermediate_endpoints
#print axioms Nock.NockVMROM.Thm54.GateCorrespondenceMemory.selectorEquality_vanishes_on_mirror_binding
