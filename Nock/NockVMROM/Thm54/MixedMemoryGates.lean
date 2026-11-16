/-
  Nock/NockVMROM/Thm54/MixedMemoryGates.lean

  **The four compressed memory scalar gates, rewritten as single mixed `𝕂`-valued gates.**

  The deployed memory chip commits four base-field gates that are *scalar random-linear
  combinations* of three coordinate bodies each:

  | deployed gate | coin | coordinate bodies |
  |---|---|---|
  | `firstMaskBindingGate` | `.chal 1` | `maskBindingCoord b 47 4 k` |
  | `lastMaskBindingGate`  | `.chal 2` | `maskBindingCoord b 48 5 k` |
  | `intermediateChainGate`| `.chal 3` | `chainCoord k` |
  | `selectorEquality s`   | `.chal 0` | `selectorEqualityCoord b s k` |

  Each compression buys `3 → 1` gates and pays a **collision event**: the RLC can vanish while its
  coordinates do not, so recovering the coordinates needs the coin to miss a bad-challenge set.
  Those four events are four of the five conjuncts of `RepairedMemoryCollisionGood`, and they are
  the whole memory half of the released bound's `(20 + 14·M)/|𝔽|` summand.

  Written as `MixedCoordinateCompiler.MixedExpr` gates, they need no coin at all:
  `mixedCompile_zero_iff` says one mixed `𝕂`-equation **is** its `e` coordinate equations, because
  `∑ₖ cₖ·bₖ = 0 ↔ ∀ k, cₖ = 0` holds for a basis with no randomness anywhere.

  **The three `rfl`s are the point.**  At the deployed layout `(memorySourceTemplate b).col0 3`,
  `mixedCompile` of the mask and selector gates produces bodies **definitionally equal** to the
  coordinate bodies the chip already commits — so a chip that commits the mixed gate commits
  exactly the same polynomials, minus the compression.  For the chain gate this is true only
  through `Scale`: routed through `Mul` the compiler goes to `mulVec`'s `e²`-term tensor
  contraction and the compiled body is correct but *not* the deployed one (measured: `rfl` fails
  with "Not a definitional equality"), which is why `Scale` is a constructor rather than sugar.

  SCOPE, as of stage 3b.  The gates themselves now live in `OptimizedMemoryGateBasis` and
  `memorySourceTemplate` **commits them**: `mixedTransition := mixedTransitionGates b` and
  `equalityChecks b := mixedExpandList b memoryCol0 (mixedEqualityChecks b)`.
-/

import Nock.NockVMROM.Thm54.MixedCoordinateCompiler
import Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting

namespace Nock.NockVMROM.Thm54
namespace MixedMemoryGates

open Nock.Reified
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Module

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- The deployed memory chip's coordinate layout. -/
abbrev memCol0 (b : Basis (Fin 3) F K) : VarKind → ℕ → ℕ := (memorySourceTemplate b).col0 3

/-! ## 1. The four gates

**Stage 3b: these are now the chip's own gates.**  The four definitions
`firstMaskMixed`, `lastMaskMixed`, `selectorMixed` and `chainMixed`, together with the two lists
`mixedTransitionGates` / `mixedEqualityChecks`, live in `OptimizedMemoryGateBasis` — upstream of
this module — because `memorySourceTemplate` commits them.  They are *not* re-declared here: this
module `open`s that namespace, so every theorem below is about the gates the deployed chip
actually commits, not about a definitionally-equal copy. -/

/-! ## 2. Degrees — inside the paper's budgets

the paper bounds memory transition gates by degree `4`; `:1489`'s equality checks are
linear.  The mask and selector gates are degree `1`, the chain gate degree `2`, so the mixed
bucket costs the same degree budget as the base gates it replaces — and the paper's
degree-`1` endpoint budget would also accept the three linear ones. -/

omit [Field F] [FiniteDimensional F K] in
theorem firstMaskMixed_degree : (firstMaskMixed (F := F)).degree = 1 := rfl
omit [Field F] [FiniteDimensional F K] in
theorem lastMaskMixed_degree : (lastMaskMixed (F := F)).degree = 1 := rfl
omit [Field F] [FiniteDimensional F K] in
theorem dequeueMaskMixed_degree : (dequeueMaskMixed (F := F)).degree = 1 := rfl
omit [Field F] [FiniteDimensional F K] in
theorem selectorMixed_degree (s : Fin 4) : (selectorMixed (F := F) s).degree = 1 := rfl
omit [FiniteDimensional F K] in
theorem chainMixed_degree : (chainMixed (F := F)).degree = 2 := rfl
omit [FiniteDimensional F K] in
theorem accChainMixed_degree : (accChainMixed (F := F)).degree = 2 := rfl
omit [Field F] [FiniteDimensional F K] in
theorem denominatorPinMixed_degree : (denominatorPinMixed (F := F)).degree = 1 := rfl

/-! ## 3. The compiled bodies ARE the deployed coordinate bodies

Three `rfl`s and one `rfl` that needs `Scale`.  These are what make the promotion a *retyping*
of the chip's existing polynomials rather than a rewrite of them. -/

/-- **`rfl` 1.** -/
theorem firstMaskMixed_compiles_to_deployed (b : Basis (Fin 3) F K) (k : Fin 3) :
    mixedCompile b (memCol0 b) (firstMaskMixed (F := F)) k = maskBindingCoord b 47 4 k := rfl

/-- **`rfl` 2.** -/
theorem lastMaskMixed_compiles_to_deployed (b : Basis (Fin 3) F K) (k : Fin 3) :
    mixedCompile b (memCol0 b) (lastMaskMixed (F := F)) k = maskBindingCoord b 48 5 k := rfl

theorem dequeueMaskMixed_compiles_to_deployed (b : Basis (Fin 3) F K) (k : Fin 3) :
    mixedCompile b (memCol0 b) (dequeueMaskMixed (F := F)) k = maskBindingCoord b 56 154 k := rfl

/-- **`rfl` 3.** -/
theorem selectorMixed_compiles_to_deployed (b : Basis (Fin 3) F K) (s : Fin 4) (k : Fin 3) :
    mixedCompile b (memCol0 b) (selectorMixed (F := F) s) k = selectorEqualityCoord b s k := rfl

/-- **`rfl` 4 — and it is the reason `Scale` is a constructor.**  Written as
`Mul (Lift (1 - bcur 5)) (…)` the compiler routes the base-field mask through `mulVec`'s
`e²`-term tensor contraction; the result is semantically correct (`mixedCompile_eval` holds for
it) but is **not** `chainCoord k`, and `rfl` fails.  Through `Scale` it is definitional. -/
theorem chainMixed_compiles_to_deployed (b : Basis (Fin 3) F K) (k : Fin 3) :
    mixedCompile b (memCol0 b) (chainMixed (F := F)) k = chainCoord (F := F) k := rfl

/-- The response-accumulator chain compiles to its three coordinate
bodies `accChainCoord k`, through `Scale` like `chainMixed`. -/
theorem accChainMixed_compiles_to_deployed (b : Basis (Fin 3) F K) (k : Fin 3) :
    mixedCompile b (memCol0 b) (accChainMixed (F := F)) k = accChainCoord (F := F) k := rfl

/-- The `k`-th committed coordinate body of the response-denominator pin (A-mem-2).  Unlike the
mask, chain and accumulator-chain bodies it has no hand-written twin in `OptimizedMemoryGateBasis`:
the pin multiplies the `𝕂` challenge `γ^c` into the `𝕂` record fields, so its coordinate bodies
go through `mulVec`/`powVec` and depend on the basis `b`.  It is named here so the expanded bucket
can be listed in order. -/
def denominatorPinCoord (b : Basis (Fin 3) F K) (k : Fin 3) : CoeffExpr F :=
  mixedCompile b (memCol0 b) (denominatorPinMixed (F := F)) k

theorem mixedTransitionGates_expand (b : Basis (Fin 3) F K) :
    mixedExpandList b (memCol0 b) (foldedMixedTransitionGates (F := F)) =
      [maskBindingCoord b 47 4 0, maskBindingCoord b 47 4 1, maskBindingCoord b 47 4 2,
       maskBindingCoord b 48 5 0, maskBindingCoord b 48 5 1, maskBindingCoord b 48 5 2,
       chainCoord (F := F) 0, chainCoord (F := F) 1, chainCoord (F := F) 2,
       accChainCoord (F := F) 0, accChainCoord (F := F) 1, accChainCoord (F := F) 2,
       denominatorPinCoord b 0, denominatorPinCoord b 1, denominatorPinCoord b 2,
       maskBindingCoord b 56 154 0, maskBindingCoord b 56 154 1,
       maskBindingCoord b 56 154 2] := rfl

/-- The expanded mixed equality bucket is exactly the twelve deployed selector mirror
coordinates — `4 · e = 12`. -/
theorem mixedEqualityChecks_expand_length (b : Basis (Fin 3) F K) :
    (mixedExpandList b (memCol0 b) (mixedEqualityChecks b)).length = 12 := by
  rw [length_mixedExpandList, mixedEqualityChecks_length]

theorem mem_mixedEqualityChecks_expand (b : Basis (Fin 3) F K) (u : CoeffExpr F) :
    u ∈ mixedExpandList b (memCol0 b) (mixedEqualityChecks b) ↔
      ∃ (s : Fin 4) (k : Fin 3), u = selectorEqualityCoord b s k := by
  rw [mem_mixedExpandList]
  constructor
  · rintro ⟨g, hg, k, rfl⟩
    obtain ⟨s, -, rfl⟩ := List.mem_ofFn.mp hg
    exact ⟨s, k, (selectorMixed_compiles_to_deployed b s k)⟩
  · rintro ⟨s, k, rfl⟩
    exact ⟨selectorMixed s, List.mem_ofFn.mpr ⟨s, rfl⟩, k,
      (selectorMixed_compiles_to_deployed b s k).symm⟩

/-! ## 4. What committing them buys: four of the five conjuncts, for free -/

theorem firstMaskMixed_zero_iff (b : Basis (Fin 3) F K) (envF : Env F) :
    (firstMaskMixed (F := F)).eval (gatherEnv b (memCol0 b) envF) envF = 0
      ↔ ∀ k : Fin 3, (maskBindingCoord b 47 4 k).eval envF = 0 :=
  mixedCompile_zero_iff b (memCol0 b) (isCoordEnv_gather b (memCol0 b) envF) _

theorem lastMaskMixed_zero_iff (b : Basis (Fin 3) F K) (envF : Env F) :
    (lastMaskMixed (F := F)).eval (gatherEnv b (memCol0 b) envF) envF = 0
      ↔ ∀ k : Fin 3, (maskBindingCoord b 48 5 k).eval envF = 0 :=
  mixedCompile_zero_iff b (memCol0 b) (isCoordEnv_gather b (memCol0 b) envF) _

theorem chainMixed_zero_iff (b : Basis (Fin 3) F K) (envF : Env F) :
    (chainMixed (F := F)).eval (gatherEnv b (memCol0 b) envF) envF = 0
      ↔ ∀ k : Fin 3, (chainCoord (F := F) k).eval envF = 0 :=
  mixedCompile_zero_iff b (memCol0 b) (isCoordEnv_gather b (memCol0 b) envF) _

theorem accChainMixed_zero_iff (b : Basis (Fin 3) F K) (envF : Env F) :
    (accChainMixed (F := F)).eval (gatherEnv b (memCol0 b) envF) envF = 0
      ↔ ∀ k : Fin 3, (accChainCoord (F := F) k).eval envF = 0 :=
  mixedCompile_zero_iff b (memCol0 b) (isCoordEnv_gather b (memCol0 b) envF) _

theorem denominatorPinMixed_zero_iff (b : Basis (Fin 3) F K) (envF : Env F) :
    (denominatorPinMixed (F := F)).eval (gatherEnv b (memCol0 b) envF) envF = 0
      ↔ ∀ k : Fin 3, (denominatorPinCoord b k).eval envF = 0 :=
  mixedCompile_zero_iff b (memCol0 b) (isCoordEnv_gather b (memCol0 b) envF) _

theorem selectorMixed_zero_iff (b : Basis (Fin 3) F K) (envF : Env F) (s : Fin 4) :
    (selectorMixed (F := F) s).eval (gatherEnv b (memCol0 b) envF) envF = 0
      ↔ ∀ k : Fin 3, (selectorEqualityCoord b s k).eval envF = 0 :=
  mixedCompile_zero_iff b (memCol0 b) (isCoordEnv_gather b (memCol0 b) envF) _

/-- **THE PRIZE.  Committing the four mixed gates discharges four of the five conjuncts of
`RepairedMemoryCollisionGood` unconditionally** — no coin, no bad-challenge set, no collision
event.

The reason is structural: the RLC compression exists only to squeeze three base-field equations
into one base-field gate, saving two gates; its price is a coin and a collision event.  A
`𝕂`-typed gate **is** its `e` coordinate equations, so it buys the same conclusion for the same
three gates and no coin. -/
theorem four_conjuncts_for_free (b : Basis (Fin 3) F K) (envF : Env F)
    (h1 : (firstMaskMixed (F := F)).eval (gatherEnv b (memCol0 b) envF) envF = 0)
    (h2 : (lastMaskMixed (F := F)).eval (gatherEnv b (memCol0 b) envF) envF = 0)
    (h3 : (chainMixed (F := F)).eval (gatherEnv b (memCol0 b) envF) envF = 0)
    (h4 : ∀ s : Fin 4,
      (selectorMixed (F := F) s).eval (gatherEnv b (memCol0 b) envF) envF = 0) :
    FirstMaskCollisionExcluded b envF ∧ LastMaskCollisionExcluded b envF ∧
      ChainCollisionExcluded (F := F) envF ∧ SelectorEqualityCollisionExcluded b envF :=
  ⟨fun _ => (firstMaskMixed_zero_iff b envF).1 h1,
   fun _ => (lastMaskMixed_zero_iff b envF).1 h2,
   fun _ => (chainMixed_zero_iff b envF).1 h3,
   fun s _ k => (selectorMixed_zero_iff b envF s).1 (h4 s) k⟩

theorem four_conjuncts_from_expanded_buckets (b : Basis (Fin 3) F K) (envF : Env F)
    (htr : ∀ u ∈ mixedExpandList b (memCol0 b) (foldedMixedTransitionGates (F := F)),
      u.eval envF = 0)
    (heq : ∀ u ∈ mixedExpandList b (memCol0 b) (mixedEqualityChecks b), u.eval envF = 0) :
    FirstMaskCollisionExcluded b envF ∧ LastMaskCollisionExcluded b envF ∧
      ChainCollisionExcluded (F := F) envF ∧ SelectorEqualityCollisionExcluded b envF := by
  have hK := (mixedExpandList_zero_iff b (memCol0 b)
    (isCoordEnv_gather b (memCol0 b) envF) (foldedMixedTransitionGates (F := F))).1 htr
  have hE := (mixedExpandList_zero_iff b (memCol0 b)
    (isCoordEnv_gather b (memCol0 b) envF) (mixedEqualityChecks b)).1 heq
  refine four_conjuncts_for_free b envF
    (hK _ (by simp [foldedMixedTransitionGates]))
    (hK _ (by simp [foldedMixedTransitionGates]))
    (hK _ (by simp [foldedMixedTransitionGates]))
    (fun s => hE _ (List.mem_ofFn.mpr ⟨s, rfl⟩))

/-- **The residual, named.**  `ExtensionChallengeMigration` carries
`GatheredScalarGatesVanish`'s conclusions as an explicit hypothesis on
`OptimizedProductionAcceptanceAtK` because the deployed chip cannot supply them
(`deployed_chip_does_not_supply_memory_gathered_gates`).  The mixed gates supply them directly,
with no extension coin appearing anywhere. -/
theorem gathered_conclusions_without_any_coin (b : Basis (Fin 3) F K) (envF : Env F)
    (h1 : (firstMaskMixed (F := F)).eval (gatherEnv b (memCol0 b) envF) envF = 0)
    (h2 : (lastMaskMixed (F := F)).eval (gatherEnv b (memCol0 b) envF) envF = 0)
    (h4 : ∀ s : Fin 4,
      (selectorMixed (F := F) s).eval (gatherEnv b (memCol0 b) envF) envF = 0) :
    (∀ k : Fin 3, (maskBindingCoord b 47 4 k).eval envF = 0) ∧
      (∀ k : Fin 3, (maskBindingCoord b 48 5 k).eval envF = 0) ∧
      (∀ (s : Fin 4) (k : Fin 3), (selectorEqualityCoord b s k).eval envF = 0) :=
  ⟨(firstMaskMixed_zero_iff b envF).1 h1,
   (lastMaskMixed_zero_iff b envF).1 h2,
   fun s k => (selectorMixed_zero_iff b envF s).1 (h4 s) k⟩

/-! ## 5. The ledger of the landed promotion

`s` moves by `+(e−1)` per promoted gate and `w` does not move at all, because the mixed gates read
columns that already exist.  Stated here as arithmetic over the deployed list lengths so that the
numerals in `Thm54Resources` and `RAPPadding` can be checked against it. -/

/-- Base transition gates after the promotion: `14 − 3 = 11`. -/
def promotedBaseTransitionCount : ℕ := 11

/-- `𝕂`-valued transition gates after the promotion, the accumulator chain, the denominator
pin and the dequeue-mask pin: `21 + 6 = 27`. -/
def promotedExtTransitionCount : ℕ := 27

/-- Equality checks after the promotion: `4` `𝕂`-valued gates, i.e. `4·e = 12` base gates. -/
def promotedEqualityCheckCount : ℕ := 4

/-- The promoted counts are the folded list lengths, not numerals chosen to fit. -/
theorem promoted_counts_from_folded_lengths (b : Basis (Fin 3) F K) :
    promotedBaseTransitionCount = (foldedBaseTransitionGates b).length ∧
      promotedExtTransitionCount
        = extensionTransitionGates (K := K).length + (foldedMixedTransitionGates (F := F)).length ∧
      promotedEqualityCheckCount = (mixedEqualityChecks b).length ∧
      promotedEqualityCheckCount * 3 = (foldedEqualityChecks b).length := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [foldedBaseTransitionGates_length]; rfl
  · rw [extensionTransitionGates_length, foldedMixedTransitionGates_length]; rfl
  · rw [mixedEqualityChecks_length]; rfl
  · rw [foldedEqualityChecks_length]; rfl

theorem w2_committed_counts (b : Basis (Fin 3) F K) :
    (baseTransitionGates b).length = 6 ∧
      (mixedTransitionGates (F := F) (K := K) b).length = 50 ∧
      (equalityChecks b).length = 0 ∧
      (baseTransitionGates b).length + (mixedTransitionGates b).length * 3 = 156 := by
  refine ⟨baseTransitionGates_length b, mixedTransitionGates_length b,
    equalityChecks_length b, ?_⟩
  rw [baseTransitionGates_length, mixedTransitionGates_length]

theorem promotion_gate_ledger (b : Basis (Fin 3) F K) :
    (foldedBaseTransitionGates b).length
        + (extensionTransitionGates (K := K).length + (foldedMixedTransitionGates (F := F)).length) * 3 = 92 ∧
      (foldedEqualityChecks b).length = 12 ∧
      (77 : ℕ) + 4 = 81 ∧
      89 + 12 = 101 ∧
      (83 + 12) - (77 + 4) = 14 ∧ (86 + 12) - (83 + 12) = 3 ∧ (89 + 12) - (86 + 12) = 3 := by
  refine ⟨?_, foldedEqualityChecks_length b, by decide, by decide, by decide, by decide, by decide⟩
  rw [foldedBaseTransitionGates_length, extensionTransitionGates_length,
    foldedMixedTransitionGates_length]

/-- No selector, mask or chain coin appears anywhere in the
hypotheses.

So the `14·M/|𝔽|` summand of `optimizedMergedProductionFailureProbabilityBound` was not merely
*unused*: it priced randomness against compressed gates that are **not in the committed system**
(`GatheredMemoryScalarGates.the_four_scalar_gates_are_retyped`: the base list is `11` and the
equality list `12`, and the four compressed gates are in neither).  That is the argument for
deleting those four lifts from the failure union, which
`OptimizedMemoryCollisionAccounting.extensionMemoryCollisionEvent` does. -/
theorem repaired_good_from_committed_buckets_and_fold
    (b : Basis (Fin 3) F K) (envF : Env F) (envK : Env K)
    (htr : ∀ u ∈ mixedExpandList b (memCol0 b) (foldedMixedTransitionGates (F := F)),
      u.eval envF = 0)
    (heq : ∀ u ∈ mixedExpandList b (memCol0 b) (mixedEqualityChecks b), u.eval envF = 0)
    (hfold : FoldCollisionExcluded envK) :
    RepairedMemoryCollisionGood b envF envK := by
  obtain ⟨h1, h2, h3, h4⟩ := four_conjuncts_from_expanded_buckets b envF htr heq
  exact ⟨hfold, h1, h2, h3, h4⟩

end
end MixedMemoryGates
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.MixedMemoryGates.chainMixed_compiles_to_deployed
#print axioms Nock.NockVMROM.Thm54.MixedMemoryGates.mixedTransitionGates_expand
#print axioms Nock.NockVMROM.Thm54.MixedMemoryGates.four_conjuncts_for_free
#print axioms Nock.NockVMROM.Thm54.MixedMemoryGates.four_conjuncts_from_expanded_buckets
#print axioms Nock.NockVMROM.Thm54.MixedMemoryGates.gathered_conclusions_without_any_coin
#print axioms Nock.NockVMROM.Thm54.MixedMemoryGates.promotion_gate_ledger
#print axioms Nock.NockVMROM.Thm54.MixedMemoryGates.repaired_good_from_committed_buckets_and_fold
