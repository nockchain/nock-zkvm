/-
  Nock/NockVMROM/Thm54/GatheredMemoryScalarGates.lean

  **The four memory scalar-compression gates, recompiled to the gathered `Env 𝕂` level.**

  This module supplies exactly those four gates at the gathered extension level, and the two
  bridges over `MemoryChallengeTupleK` (`ExtensionChallenges.lean:171`).  It is **additive**:
  nothing existing is edited, and `OptimizedStrictFullPackage.lean` still consumes the `𝔽`-typed
  bound.

  §1 is the compression coin drawn from `𝕂`.  The coin is read out of a *gathered* environment
  (`gatherEnv`, `CoordinateRAPCore.lean:186`), whose challenge slot `j` is the basis combination
  of the three consecutive base-field slots `col0.challenge j + 0,1,2` (`:189`) — the deployed
  client's `make-pelt-chal`, which builds
  every challenge as a three-coefficient `bpoly` from the draws `<name>-a`, `<name>-b`, `<name>-c`
  (`five.hoon:150`, routed by `init-ext-chals`, `seven.hoon:323`, over `chal-names-rd1`,
  `:288`, and `init-mega-ext-chals`, `:395`, over `chal-names-rd2`, `:346`).

  §4 is the finding.  **The re-typing is sound but it is not yet consumable, and the reason is
  not the collision counting.**  A `𝕂`-valued gate is not a member of either gate
  category the chip template offers — `baseTransition : List (CoeffExpr 𝔽)` or
  `extTransition : List Expr` read in the gathered `Env 𝕂` — because the mask/selector/chain
  bodies mix a `𝕂` challenge with *base* trace columns (`bcur 4`, `bcur 5`, `bcur s`) that lie
  below `baseCols = 6` and are therefore not addressable as gathered `𝕂` columns.  Enforcing the
  `𝕂` equation at all means committing its three coordinates, i.e. three `CoeffExpr 𝔽` gates
  where the deployed AIR has one (`extension_gate_costs_three_base_gates`).  All four gates are
  live members of the memory chip's committed lists, so that change moves
  `(memorySourceTemplate b).baseTransition.length` and hence the memory chip's constraint count,
  which `OptimizedFullCostRealization.exact_resources` pins.

  The paragraph below
  is kept because it is the reasoning that predicted the cost, and it predicted it correctly.  `base_gate_is_strictly_weaker_than_gathered_gate` compiles the underlying
  fact: a trace can satisfy the deployed base gate while violating the `𝕂` gate.

  A second observation, recorded because it changes the recommendation: for the three-term
  families the compression is *dominated*.  Enforcing the three coordinate equations directly
  costs the same three `CoeffExpr 𝔽` gates as the coordinate expansion of the `𝕂` gate, needs no
  coin at all, and has no collision event
  (`uncompressed_costs_the_same_and_has_no_collision_event`).  Only the compute chip's
  eleven-term `challenge36` families (`OptimizedComputeCollisionBound.lean:518`) are a case where
  re-typing beats de-compression.
-/
import Nock.NockVMROM.Thm54.ExtensionChallenges

set_option autoImplicit false
set_option maxRecDepth 8000

namespace Nock.NockVMROM.Thm54
namespace GatheredMemoryScalarGates

open scoped Classical Polynomial
open Polynomial
open Nock.Framework
open Nock.Reified
open Module
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.ExtensionChallenges

noncomputable section

/-! ## 1. The compression coin, drawn from `𝕂`

`rlc3` (`OptimizedMemoryGateBasis.lean:669`) compresses three base-field coordinate bodies at a
base-field coin.  `gatheredRlc3` is the same random linear combination at a coin of `𝕂`, with the
coordinate bodies widened along `algebraMap 𝔽 𝕂`. -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The three coordinate values, compressed at an extension-field coin.  Same shape as
`rlc3` (`OptimizedMemoryGateBasis.lean:669`), with the coin in `𝕂` and the coordinate bodies
widened along `algebraMap 𝔽 𝕂`. -/
def gatheredRlc3 (ρ : K) (c : Fin 3 → F) : K :=
  algebraMap F K (c 0) + ρ * algebraMap F K (c 1) + ρ ^ 2 * algebraMap F K (c 2)

/-- The compressed value is the `𝕂`-evaluation of `JV`'s widened RLC polynomial, so
`liftedValueBadChallenges_card_le` (`ExtensionChallenges.lean:140`) is its root count. -/
theorem gatheredRlc3_eq_eval (ρ : K) (c : Fin 3 → F) :
    gatheredRlc3 ρ c =
      (valueRlcPolynomial (liftValues (K := K) (List.ofFn c))).eval ρ := by
  simp [gatheredRlc3, liftValues, valueRlcPolynomial]
  ring

/-- **Compatibility.**  At a coin that happens to lie in the base field the gathered
combination is the image of the existing base-field one: this widens the challenge domain, it
does not change the constraint. -/
theorem gatheredRlc3_algebraMap (ρ : F) (c : Fin 3 → F) :
    gatheredRlc3 (algebraMap F K ρ) c =
      algebraMap F K (c 0 + ρ * c 1 + ρ ^ 2 * c 2) := by
  simp [gatheredRlc3, map_add, map_mul, map_pow]

/-- The base-field gate body, as an explicit three-term sum. -/
theorem rlc3_eval_eq_three_terms (ρe : CoeffExpr F) (f : Fin 3 → CoeffExpr F) (env : Env F) :
    (rlc3 ρe f).eval env =
      (f 0).eval env + ρe.eval env * (f 1).eval env
        + (ρe.eval env) ^ 2 * (f 2).eval env := by
  simp [rlc3, CoeffExpr.sumList, List.finRange, CoeffExpr.eval]
  ring

/-- `selectorEquality` (`OptimizedMemoryGateBasis.lean:837`) is the same three-term compression
at `selectorEqualityCoord` (`OptimizedMemoryCollisionAccounting.lean:479`). -/
theorem selectorEquality_eq_rlc3 (b : Basis (Fin 3) F K) (s : Fin 4) :
    selectorEquality b s = rlc3 selectorEqualityChallenge (selectorEqualityCoord b s) := rfl

/-! ## 2. The four gates, recompiled

Fresh extension challenge indices.  The memory chip's committed `𝕂` challenge indices are
`0..2` (memory), `3` (forest) and `6` (extension fold) — `OptimizedMemoryGateBasis.lean:10`,
`:40`, `:56`, `:446` — so `7..10` do not alias any of them. -/

def selectorEqualityChallengeK : ℕ := 7
def firstMaskBindingChallengeK : ℕ := 8
def lastMaskBindingChallengeK : ℕ := 9
def chainBindingChallengeK : ℕ := 10

/-- The four fresh coins alias no committed memory/forest/fold `𝕂` challenge index. -/
theorem gathered_scalar_challenges_fresh :
    ({selectorEqualityChallengeK, firstMaskBindingChallengeK, lastMaskBindingChallengeK,
        chainBindingChallengeK} : Finset ℕ) ∩ ({0, 1, 2, 3, 6} : Finset ℕ) = ∅ := by
  decide

/-- `selectorEquality` (`OptimizedMemoryGateBasis.lean:837`) at an extension coin. -/
def selectorEqualityGateK (b : Basis (Fin 3) F K) (envK : Env K) (envF : Env F)
    (s : Fin 4) : K :=
  gatheredRlc3 (envK.chal selectorEqualityChallengeK)
    (fun k => (selectorEqualityCoord b s k).eval envF)

/-- `firstMaskBindingGate` (`OptimizedMemoryGateBasis.lean:673`) at an extension coin. -/
def firstMaskBindingGateK (b : Basis (Fin 3) F K) (envK : Env K) (envF : Env F) : K :=
  gatheredRlc3 (envK.chal firstMaskBindingChallengeK)
    (fun k => (maskBindingCoord b 47 4 k).eval envF)

/-- `lastMaskBindingGate` (`OptimizedMemoryGateBasis.lean:677`) at an extension coin. -/
def lastMaskBindingGateK (b : Basis (Fin 3) F K) (envK : Env K) (envF : Env F) : K :=
  gatheredRlc3 (envK.chal lastMaskBindingChallengeK)
    (fun k => (maskBindingCoord b 48 5 k).eval envF)

/-- `intermediateChainGate` (`OptimizedMemoryGateBasis.lean:685`) at an extension coin. -/
def intermediateChainGateK (envK : Env K) (envF : Env F) : K :=
  gatheredRlc3 (envK.chal chainBindingChallengeK)
    (fun k => (chainCoord (F := F) k).eval envF)

/-- **The coin is `make-pelt-chal`.**  Read out of a gathered environment, each of the four
coins is the basis combination of three consecutive base-field challenge slots — the deployed
client's three-coefficient `bpoly` (`five.hoon:159`). -/
theorem gathered_coin_is_three_base_slots
    (b : Basis (Fin 3) F K) (col0 : VarKind → ℕ → ℕ) (envF : Env F) (j : ℕ) :
    (gatherEnv b col0 envF).chal j =
      ∑ k : Fin 3, envF.chal (col0 .challenge j + (k : ℕ)) • b k := rfl

/-- **Compatibility, first mask.** -/
theorem firstMaskBindingGateK_of_base
    (b : Basis (Fin 3) F K) (envK : Env K) (envF : Env F)
    (h : envK.chal firstMaskBindingChallengeK = algebraMap F K (envF.chal 1)) :
    firstMaskBindingGateK b envK envF =
      algebraMap F K ((firstMaskBindingGate b).eval envF) := by
  rw [firstMaskBindingGateK, h, gatheredRlc3_algebraMap, firstMaskBindingGate,
    rlc3_eval_eq_three_terms]
  rfl

/-- **The only way the deployed chip can feed the gathered bridge.**  The memory chip commits
`firstMaskBindingGate`, not the gathered gate, so the sole route from an accepted trace to
`FirstMaskCollisionExcludedK` is `firstMaskBindingGateK_of_base` — and that route pins the coin
into `algebraMap 𝔽 𝕂`'s range, i.e. back to a base-field sample space of `|𝔽|` points.  The
`𝕂`-typed bound is therefore not consumable while the chip's gate stays base-field: it is the
*gate*, not the counting, that has to move. -/
theorem feeding_the_gathered_gate_from_the_base_gate_needs_a_base_field_coin
    (b : Basis (Fin 3) F K) (envK : Env K) (envF : Env F)
    (h : envK.chal firstMaskBindingChallengeK = algebraMap F K (envF.chal 1))
    (hbase : (firstMaskBindingGate b).eval envF = 0) :
    firstMaskBindingGateK b envK envF = 0 ∧
      envK.chal firstMaskBindingChallengeK ∈ Set.range (algebraMap F K) := by
  refine ⟨?_, ⟨envF.chal 1, h.symm⟩⟩
  rw [firstMaskBindingGateK_of_base b envK envF h, hbase, map_zero]

/-- **Compatibility, last mask.** -/
theorem lastMaskBindingGateK_of_base
    (b : Basis (Fin 3) F K) (envK : Env K) (envF : Env F)
    (h : envK.chal lastMaskBindingChallengeK = algebraMap F K (envF.chal 2)) :
    lastMaskBindingGateK b envK envF =
      algebraMap F K ((lastMaskBindingGate b).eval envF) := by
  rw [lastMaskBindingGateK, h, gatheredRlc3_algebraMap, lastMaskBindingGate,
    rlc3_eval_eq_three_terms]
  rfl

/-- **Compatibility, intermediate chain.** -/
theorem intermediateChainGateK_of_base
    (envK : Env K) (envF : Env F)
    (h : envK.chal chainBindingChallengeK = algebraMap F K (envF.chal 3)) :
    intermediateChainGateK (F := F) envK envF =
      algebraMap F K ((intermediateChainGate (F := F)).eval envF) := by
  rw [intermediateChainGateK, h, gatheredRlc3_algebraMap, intermediateChainGate,
    rlc3_eval_eq_three_terms]
  rfl

/-- **Compatibility, selector equality.** -/
theorem selectorEqualityGateK_of_base
    (b : Basis (Fin 3) F K) (envK : Env K) (envF : Env F) (s : Fin 4)
    (h : envK.chal selectorEqualityChallengeK = algebraMap F K (envF.chal 0)) :
    selectorEqualityGateK b envK envF s =
      algebraMap F K ((selectorEquality b s).eval envF) := by
  rw [selectorEqualityGateK, h, gatheredRlc3_algebraMap, selectorEquality_eq_rlc3,
    rlc3_eval_eq_three_terms]
  rfl

/-! ## 3. The gate-to-event bridges at the new typing

The `𝕂`-level collision exclusions have **exactly the conclusions** of the base-field ones
(`OptimizedMemoryGateBasis.lean:599,784,788,792,847`); only the trigger moved to the gathered
gate. -/

def FirstMaskCollisionExcludedK (b : Basis (Fin 3) F K) (envF : Env F) (envK : Env K) : Prop :=
  firstMaskBindingGateK b envK envF = 0 →
    ∀ k : Fin 3, (maskBindingCoord b 47 4 k).eval envF = 0

def LastMaskCollisionExcludedK (b : Basis (Fin 3) F K) (envF : Env F) (envK : Env K) : Prop :=
  lastMaskBindingGateK b envK envF = 0 →
    ∀ k : Fin 3, (maskBindingCoord b 48 5 k).eval envF = 0

def ChainCollisionExcludedK (envF : Env F) (envK : Env K) : Prop :=
  intermediateChainGateK (F := F) envK envF = 0 →
    ∀ k : Fin 3, (chainCoord (F := F) k).eval envF = 0

def SelectorEqualityCollisionExcludedK
    (b : Basis (Fin 3) F K) (envF : Env F) (envK : Env K) : Prop :=
  ∀ s : Fin 4, selectorEqualityGateK b envK envF s = 0 →
    ∀ k : Fin 3,
      (CoeffExpr.sub
        (CoeffExpr.var .traceCur (6 + 3 * (51 + s) + k))
        (CoeffExpr.mul (CoeffExpr.const (coord b (1 : K) ⟨k, by omega⟩))
          (CoeffExpr.var .traceCur s))).eval envF = 0

/-- The `𝕂`-typed analogue of `RepairedMemoryCollisionGood`
(`OptimizedMemoryCollisionAccounting.lean:465`), conjunct for conjunct in the same order. -/
def RepairedMemoryCollisionGoodK
    (b : Basis (Fin 3) F K) (envF : Env F) (envK : Env K) : Prop :=
  FoldCollisionExcluded envK ∧
  FirstMaskCollisionExcludedK b envF envK ∧
  LastMaskCollisionExcludedK b envF envK ∧
  ChainCollisionExcludedK (K := K) envF envK ∧
  SelectorEqualityCollisionExcludedK b envF envK

/-- **Nothing is lost by re-typing the exclusions.**  Each `𝕂`-level conjunct has the same
conclusion as the corresponding base-field conjunct of `RepairedMemoryCollisionGood`, so a
consumer of the base-field bundle can be fed by the extension one once the gates agree. -/
theorem repairedMemoryCollisionGoodK_conclusions_match
    (b : Basis (Fin 3) F K) (envF : Env F) (envK : Env K)
    (h : RepairedMemoryCollisionGoodK b envF envK)
    (hfirst : firstMaskBindingGateK b envK envF = 0)
    (hlast : lastMaskBindingGateK b envK envF = 0)
    (hchain : intermediateChainGateK (F := F) envK envF = 0)
    (hsel : ∀ s : Fin 4, selectorEqualityGateK b envK envF s = 0) :
    FoldCollisionExcluded envK ∧
      (∀ k : Fin 3, (maskBindingCoord b 47 4 k).eval envF = 0) ∧
      (∀ k : Fin 3, (maskBindingCoord b 48 5 k).eval envF = 0) ∧
      (∀ k : Fin 3, (chainCoord (F := F) k).eval envF = 0) ∧
      (∀ s : Fin 4, ∀ k : Fin 3,
        (CoeffExpr.sub
          (CoeffExpr.var .traceCur (6 + 3 * (51 + s) + k))
          (CoeffExpr.mul (CoeffExpr.const (coord b (1 : K) ⟨k, by omega⟩))
            (CoeffExpr.var .traceCur s))).eval envF = 0) :=
  ⟨h.1, h.2.1 hfirst, h.2.2.1 hlast, h.2.2.2.1 hchain, fun s => h.2.2.2.2 s (hsel s)⟩

section Bridges

variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]

omit [Fintype F] [DecidableEq F] in
/-- The converse of `liftedValueCollisionExcluded_of_not_bad` (`ExtensionChallenges.lean:150`):
an exclusion at an extension coin keeps that coin out of the widened bad set. -/
theorem liftedValue_not_bad_of_collision_excluded
    (ρ : K) (as : List F)
    (hfree : (valueRlcPolynomial (liftValues (K := K) as)).eval ρ = 0 → ∀ a ∈ as, a = 0) :
    ρ ∉ liftedValueBadChallenges (K := K) as := by
  intro hbad
  have hbad' : ρ ∈ valueBadChallenges (liftValues (K := K) as) := hbad
  obtain ⟨⟨a, ha, hane⟩, hroot⟩ :=
    (mem_valueBadChallenges_iff (liftValues (K := K) as) ρ).1 hbad'
  obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
  exact hane (by simpa using congrArg (algebraMap F K) (hfree hroot a0 ha0))

omit [Fintype F] [DecidableEq F] in
/-- Coordinate projections of the all-extension memory collision event
(`ExtensionChallenges.lean:296`).  The analogue of `fullMemoryCollisionGood_components`
(`OptimizedMemoryCollisionAccounting.lean:638`). -/
theorem fullMemoryCollisionGoodK_components
    {M : ℕ} (envK : Fin M → Env K)
    (families : Fin M → Fin 7 → Fin 3 → F)
    (c : MemoryChallengeTupleK K)
    (hgood : FullMemoryCollisionGoodK envK families c) :
    c.extensionFold ∉ allMemoryExtensionBadChallenges envK ∧
      c.selectorEquality ∉ allMemorySelectorBadChallengesK (K := K) families ∧
      c.firstMask ∉ allMemoryScalarBadChallengesAtK (K := K) families 4 ∧
      c.lastMask ∉ allMemoryScalarBadChallengesAtK (K := K) families 5 ∧
      c.chain ∉ allMemoryScalarBadChallengesAtK (K := K) families 6 := by
  simp only [FullMemoryCollisionGoodK, fullMemoryCollisionEventK, Finset.mem_union,
    not_or] at hgood
  rcases hgood with ⟨⟨⟨⟨hext, hsel⟩, hfirst⟩, hlast⟩, hchain⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hext (Finset.mem_image.mpr
      ⟨(c.extensionFold, (c.selectorEquality, (c.firstMask, (c.lastMask, c.chain)))),
        by simp [h], by cases c; rfl⟩)
  · intro h
    exact hsel (Finset.mem_image.mpr
      ⟨(c.extensionFold, (c.selectorEquality, (c.firstMask, (c.lastMask, c.chain)))),
        by simp [h], by cases c; rfl⟩)
  · intro h
    exact hfirst (Finset.mem_image.mpr
      ⟨(c.extensionFold, (c.selectorEquality, (c.firstMask, (c.lastMask, c.chain)))),
        by simp [h], by cases c; rfl⟩)
  · intro h
    exact hlast (Finset.mem_image.mpr
      ⟨(c.extensionFold, (c.selectorEquality, (c.firstMask, (c.lastMask, c.chain)))),
        by simp [h], by cases c; rfl⟩)
  · intro h
    exact hchain (Finset.mem_image.mpr
      ⟨(c.extensionFold, (c.selectorEquality, (c.firstMask, (c.lastMask, c.chain)))),
        by simp [h], by cases c; rfl⟩)

omit [Fintype F] [DecidableEq F] in
/-- **Forward bridge at the new typing.**  The analogue of the removed
`repairedMemoryCollisionGood_of_full`
(`OptimizedMemoryCollisionAccounting.lean:685`), with all five pins now read out of the gathered
extension environment. -/
theorem repairedMemoryCollisionGoodK_of_full
    {M : ℕ} (b : Basis (Fin 3) F K)
    (envF : Fin M → Env F) (envK : Fin M → Env K)
    (c : MemoryChallengeTupleK K)
    (hfoldPin : ∀ i, (envK i).chal 6 = c.extensionFold)
    (hselectorPin : ∀ i, (envK i).chal selectorEqualityChallengeK = c.selectorEquality)
    (hfirstPin : ∀ i, (envK i).chal firstMaskBindingChallengeK = c.firstMask)
    (hlastPin : ∀ i, (envK i).chal lastMaskBindingChallengeK = c.lastMask)
    (hchainPin : ∀ i, (envK i).chal chainBindingChallengeK = c.chain)
    (hgood : FullMemoryCollisionGoodK envK
      (fun i => repairedMemoryScalarFamilies b (envF i)) c) :
    ∀ i, RepairedMemoryCollisionGoodK b (envF i) (envK i) := by
  have hc := fullMemoryCollisionGoodK_components envK
    (fun i => repairedMemoryScalarFamilies b (envF i)) c hgood
  intro i
  have hfoldRow : c.extensionFold ∉ extensionFoldBadChallenges (envK i) := by
    intro h
    exact hc.1 (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩)
  have scalarRow (j : Fin 7) (ρ : K)
      (hρ : ρ ∉ allMemoryScalarBadChallengesAtK (K := K)
        (fun i => repairedMemoryScalarFamilies b (envF i)) j) :
      ρ ∉ liftedValueBadChallenges (K := K)
        (List.ofFn (repairedMemoryScalarFamilies b (envF i) j)) := by
    intro h
    exact hρ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩)
  have hselectorRow (s : Fin 4) :
      c.selectorEquality ∉ liftedValueBadChallenges (K := K)
        (List.ofFn (repairedMemoryScalarFamilies b (envF i) ⟨s, by omega⟩)) := by
    apply scalarRow
    intro h
    exact hc.2.1 (Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ s, h⟩)
  have hfirstRow := scalarRow 4 c.firstMask hc.2.2.1
  have hlastRow := scalarRow 5 c.lastMask hc.2.2.2.1
  have hchainRow := scalarRow 6 c.chain hc.2.2.2.2
  refine ⟨foldCollisionExcluded_of_not_bad (envK i) ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [foldChallenge, Expr.eval, hfoldPin i] using hfoldRow
  · intro hgate k
    refine liftedValueCollisionExcluded_of_not_bad (K := K) c.firstMask
      (List.ofFn fun k : Fin 3 => (maskBindingCoord b 47 4 k).eval (envF i))
      (by simpa [repairedMemoryScalarFamilies] using hfirstRow) ?_ _
      (List.mem_ofFn.mpr ⟨k, rfl⟩)
    rw [← gatheredRlc3_eq_eval, ← hfirstPin i]
    exact hgate
  · intro hgate k
    refine liftedValueCollisionExcluded_of_not_bad (K := K) c.lastMask
      (List.ofFn fun k : Fin 3 => (maskBindingCoord b 48 5 k).eval (envF i))
      (by simpa [repairedMemoryScalarFamilies] using hlastRow) ?_ _
      (List.mem_ofFn.mpr ⟨k, rfl⟩)
    rw [← gatheredRlc3_eq_eval, ← hlastPin i]
    exact hgate
  · intro hgate k
    refine liftedValueCollisionExcluded_of_not_bad (K := K) c.chain
      (List.ofFn fun k : Fin 3 => (chainCoord (F := F) k).eval (envF i))
      (by simpa [repairedMemoryScalarFamilies] using hchainRow) ?_ _
      (List.mem_ofFn.mpr ⟨k, rfl⟩)
    rw [← gatheredRlc3_eq_eval, ← hchainPin i]
    exact hgate
  · intro s hgate k
    have hv := liftedValueCollisionExcluded_of_not_bad (K := K) c.selectorEquality
      (List.ofFn fun k : Fin 3 => (selectorEqualityCoord b s k).eval (envF i))
      (by simpa [repairedMemoryScalarFamilies] using hselectorRow s)
    refine hv ?_ _ (List.mem_ofFn.mpr ⟨k, rfl⟩)
    rw [← gatheredRlc3_eq_eval, ← hselectorPin i]
    exact hgate

omit [Fintype F] [DecidableEq F] in
/-- **Converse bridge at the new typing.**  The analogue of
the removed `fullMemoryCollisionGood_of_repaired`. -/
theorem fullMemoryCollisionGoodK_of_repaired
    {M : ℕ} (b : Basis (Fin 3) F K)
    (envF : Fin M → Env F) (envK : Fin M → Env K)
    (c : MemoryChallengeTupleK K)
    (hfoldPin : ∀ i, (envK i).chal 6 = c.extensionFold)
    (hselectorPin : ∀ i, (envK i).chal selectorEqualityChallengeK = c.selectorEquality)
    (hfirstPin : ∀ i, (envK i).chal firstMaskBindingChallengeK = c.firstMask)
    (hlastPin : ∀ i, (envK i).chal lastMaskBindingChallengeK = c.lastMask)
    (hchainPin : ∀ i, (envK i).chal chainBindingChallengeK = c.chain)
    (hgood : ∀ i, RepairedMemoryCollisionGoodK b (envF i) (envK i)) :
    FullMemoryCollisionGoodK envK
      (fun i => repairedMemoryScalarFamilies b (envF i)) c := by
  have hext : c.extensionFold ∉ allMemoryExtensionBadChallenges envK := by
    intro h
    obtain ⟨i, _hi, hibad⟩ := Finset.mem_biUnion.mp h
    exact extensionFold_not_bad_of_collision_excluded (envK i) c.extensionFold
      (by simpa only [foldChallenge, Expr.eval] using hfoldPin i) (hgood i).1 hibad
  have hselector :
      c.selectorEquality ∉ allMemorySelectorBadChallengesK (K := K)
        (fun i => repairedMemoryScalarFamilies b (envF i)) := by
    intro h
    obtain ⟨s, _hs, hsbad⟩ := Finset.mem_biUnion.mp h
    obtain ⟨i, _hi, hibad⟩ := Finset.mem_biUnion.mp hsbad
    refine liftedValue_not_bad_of_collision_excluded c.selectorEquality
      (List.ofFn (repairedMemoryScalarFamilies b (envF i) ⟨s, by omega⟩)) ?_ hibad
    intro hroot a ha
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
    have hgate : selectorEqualityGateK b (envK i) (envF i) s = 0 := by
      rw [selectorEqualityGateK, gatheredRlc3_eq_eval, hselectorPin i]
      simpa [repairedMemoryScalarFamilies] using hroot
    simpa only [repairedMemoryScalarFamilies, dif_pos s.isLt, selectorEqualityCoord] using
      (hgood i).2.2.2.2 s hgate k
  have hfirst :
      c.firstMask ∉ allMemoryScalarBadChallengesAtK (K := K)
        (fun i => repairedMemoryScalarFamilies b (envF i)) 4 := by
    intro h
    obtain ⟨i, _hi, hibad⟩ := Finset.mem_biUnion.mp h
    refine liftedValue_not_bad_of_collision_excluded c.firstMask
      (List.ofFn (repairedMemoryScalarFamilies b (envF i) 4)) ?_ hibad
    intro hroot a ha
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
    change (maskBindingCoord b 47 4 k).eval (envF i) = 0
    apply (hgood i).2.1
    rw [firstMaskBindingGateK, gatheredRlc3_eq_eval, hfirstPin i]
    simpa [repairedMemoryScalarFamilies] using hroot
  have hlast :
      c.lastMask ∉ allMemoryScalarBadChallengesAtK (K := K)
        (fun i => repairedMemoryScalarFamilies b (envF i)) 5 := by
    intro h
    obtain ⟨i, _hi, hibad⟩ := Finset.mem_biUnion.mp h
    refine liftedValue_not_bad_of_collision_excluded c.lastMask
      (List.ofFn (repairedMemoryScalarFamilies b (envF i) 5)) ?_ hibad
    intro hroot a ha
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
    change (maskBindingCoord b 48 5 k).eval (envF i) = 0
    apply (hgood i).2.2.1
    rw [lastMaskBindingGateK, gatheredRlc3_eq_eval, hlastPin i]
    simpa [repairedMemoryScalarFamilies] using hroot
  have hchain :
      c.chain ∉ allMemoryScalarBadChallengesAtK (K := K)
        (fun i => repairedMemoryScalarFamilies b (envF i)) 6 := by
    intro h
    obtain ⟨i, _hi, hibad⟩ := Finset.mem_biUnion.mp h
    refine liftedValue_not_bad_of_collision_excluded c.chain
      (List.ofFn (repairedMemoryScalarFamilies b (envF i) 6)) ?_ hibad
    intro hroot a ha
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
    change (chainCoord (F := F) k).eval (envF i) = 0
    apply (hgood i).2.2.2.1
    rw [intermediateChainGateK, gatheredRlc3_eq_eval, hchainPin i]
    simpa [repairedMemoryScalarFamilies] using hroot
  intro hbad
  simp only [fullMemoryCollisionEventK, Finset.mem_union] at hbad
  rcases hbad with ((((hbad | hbad) | hbad) | hbad) | hbad) <;>
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hbad <;>
    simp only [Finset.mem_product, Finset.mem_univ, true_and, and_true] at hq
  · exact hext hq
  · exact hselector hq
  · exact hfirst hq
  · exact hlast hq
  · exact hchain hq

end Bridges

/-! ## 4. Why the capstone cannot yet consume this

Everything above is about environments.  Consuming it at the capstone needs the *deployed AIR* to
enforce the gathered gate, and it does not. -/

section Obstruction

variable [Fintype K] [DecidableEq K]

/-- **The base gate is strictly weaker than the gathered gate.**  Outside the widened bad set a
vanishing gathered gate forces every coordinate to vanish — which is the whole content of the
re-typing. -/
theorem gatheredGate_forces_coordinates
    (b : Basis (Fin 3) F K) (envK : Env K) (envF : Env F)
    (hgood : envK.chal firstMaskBindingChallengeK ∉
      liftedValueBadChallenges (K := K)
        (List.ofFn fun k : Fin 3 => (maskBindingCoord b 47 4 k).eval envF))
    (hgate : firstMaskBindingGateK b envK envF = 0) :
    ∀ k : Fin 3, (maskBindingCoord b 47 4 k).eval envF = 0 := by
  intro k
  refine liftedValueCollisionExcluded_of_not_bad (K := K)
    (envK.chal firstMaskBindingChallengeK)
    (List.ofFn fun k : Fin 3 => (maskBindingCoord b 47 4 k).eval envF) hgood ?_ _
    (List.mem_ofFn.mpr ⟨k, rfl⟩)
  rw [← gatheredRlc3_eq_eval]
  exact hgate

/-- **The deployed base gate does not imply the gathered gate.**  A trace whose mask binding is
broken can still satisfy `firstMaskBindingGate` — the base coin is one of its at most two roots —
while the gathered gate is violated at all but at most two coins of `𝕂`.  So the extension
bridges of §3 cannot be fed by the current memory chip: the chip commits the base gate. -/
theorem base_gate_is_strictly_weaker_than_gathered_gate
    (b : Basis (Fin 3) F K) (envF : Env F)
    (hbroken : ∃ k : Fin 3, (maskBindingCoord b 47 4 k).eval envF ≠ 0)
    (hbase : (firstMaskBindingGate b).eval envF = 0)
    (hK : 2 < Fintype.card K) :
    ∃ ρ : K,
      (firstMaskBindingGate b).eval envF = 0 ∧
        gatheredRlc3 ρ (fun k : Fin 3 => (maskBindingCoord b 47 4 k).eval envF) ≠ 0 := by
  have hlen :
      (List.ofFn fun k : Fin 3 => (maskBindingCoord b 47 4 k).eval envF).length = 3 := by
    simp
  have hcard :
      (liftedValueBadChallenges (K := K)
        (List.ofFn fun k : Fin 3 => (maskBindingCoord b 47 4 k).eval envF)).card <
        (Finset.univ : Finset K).card := by
    have h := liftedValueBadChallenges_card_le (K := K)
      (List.ofFn fun k : Fin 3 => (maskBindingCoord b 47 4 k).eval envF)
    rw [hlen] at h
    rw [Finset.card_univ]
    omega
  obtain ⟨ρ, _, hρ⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨ρ, hbase, ?_⟩
  intro hzero
  obtain ⟨k, hk⟩ := hbroken
  refine hk (liftedValueCollisionExcluded_of_not_bad (K := K) ρ _ hρ ?_ _
    (List.mem_ofFn.mpr ⟨k, rfl⟩))
  rw [← gatheredRlc3_eq_eval]
  exact hzero

omit [DecidableEq K] in
/-- This used to read `firstMaskBindingGate b ∈ baseTransitionGates b ∧ … ∧
(baseTransitionGates b).length = 14 ∧ (equalityChecks b).length = 4`, and it was the receipt that
retyping them would move `memorySourceTemplate`.  It did: the memory chip now commits
`firstMaskMixed`, `lastMaskMixed` and `chainMixed` in its `𝕂`-valued `mixedTransition` bucket and
the four `selectorMixed` gates in `mixedEqualityChecks`, whose `4 · e = 12` coordinates are the
committed `equalityChecks`.  The base list fell `14 → 11` and the equality list rose `4 → 12`,
which is `M.rap.s : 104 → 112`.

The **compressed** gates `firstMaskBindingGate`, `lastMaskBindingGate`, `intermediateChainGate`
and `selectorEquality` still exist as definitions — `RepairedMemoryCollisionGood`'s conjuncts are
phrased against them — but the chip no longer commits any of them, which is exactly why
`MixedMemoryGates.four_conjuncts_for_free` can discharge four of those five conjuncts with no
coin. -/
theorem the_four_scalar_gates_are_retyped (b : Basis (Fin 3) F K) :
    firstMaskMixed (F := F) ∈ foldedMixedTransitionGates (F := F) ∧
      lastMaskMixed (F := F) ∈ foldedMixedTransitionGates (F := F) ∧
      chainMixed (F := F) ∈ mixedTransitionGates (F := F) (K := K) b ∧
      (∀ s : Fin 4,
        selectorMixed (F := F) s ∈ mixedEqualityChecks (F := F) (K := K) b) ∧
      (foldedBaseTransitionGates b).length = 11 ∧ (foldedEqualityChecks b).length = 12 := by
  refine ⟨?_, ?_, ?_, ?_, foldedBaseTransitionGates_length b, foldedEqualityChecks_length b⟩
  · simp [foldedMixedTransitionGates]
  · simp [foldedMixedTransitionGates]
  · simp [mixedTransitionGates, paperKGates, paperKGatesCore, intermediateChain]
  · intro s
    exact List.mem_ofFn.mpr ⟨s, rfl⟩

omit [DecidableEq K] in
/-- **The cost of enforcing one extension gate is three base gates.**  `expandList`
(`CoordinateRAPCore.lean:311`) commits every coordinate of an extension-level gate, so the
one-for-one replacement of a base gate by its `𝕂`-typed form is a `+2` on the chip's transition
list. -/
theorem extension_gate_costs_three_base_gates
    (b : Basis (Fin 3) F K) (col0 : VarKind → ℕ → ℕ) (g : Expr) :
    (expandList b col0 [g]).length = 3 := by
  simp [length_expandList]

omit [DecidableEq K] in
/-- **The three-term compression is dominated.**  Committing the three coordinate bodies
directly costs the same three `CoeffExpr 𝔽` gates as the coordinate expansion of the `𝕂`-typed
compression, and needs no coin: the coordinate premise is then the gate list itself, with no
collision event to exclude.  So for the memory chip's four scalar coins the repair is
de-compression, not re-typing. -/
theorem uncompressed_costs_the_same_and_has_no_collision_event
    (b : Basis (Fin 3) F K) (col0 : VarKind → ℕ → ℕ) (g : Expr) (envF : Env F)
    (h : ∀ e ∈ List.ofFn (maskBindingCoord b 47 4), (e : CoeffExpr F).eval envF = 0) :
    (List.ofFn (maskBindingCoord b 47 4)).length = (expandList b col0 [g]).length ∧
      ∀ k : Fin 3, (maskBindingCoord b 47 4 k).eval envF = 0 := by
  refine ⟨by simp [length_expandList], fun k => h _ (List.mem_ofFn.mpr ⟨k, rfl⟩)⟩

end Obstruction

end

end GatheredMemoryScalarGates
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.GatheredMemoryScalarGates.gatheredRlc3_eq_eval
#print axioms Nock.NockVMROM.Thm54.GatheredMemoryScalarGates.firstMaskBindingGateK_of_base
#print axioms Nock.NockVMROM.Thm54.GatheredMemoryScalarGates.selectorEqualityGateK_of_base
#print axioms Nock.NockVMROM.Thm54.GatheredMemoryScalarGates.feeding_the_gathered_gate_from_the_base_gate_needs_a_base_field_coin
#print axioms Nock.NockVMROM.Thm54.GatheredMemoryScalarGates.repairedMemoryCollisionGoodK_of_full
#print axioms Nock.NockVMROM.Thm54.GatheredMemoryScalarGates.fullMemoryCollisionGoodK_of_repaired
#print axioms Nock.NockVMROM.Thm54.GatheredMemoryScalarGates.base_gate_is_strictly_weaker_than_gathered_gate
#print axioms Nock.NockVMROM.Thm54.GatheredMemoryScalarGates.the_four_scalar_gates_are_retyped
#print axioms Nock.NockVMROM.Thm54.GatheredMemoryScalarGates.extension_gate_costs_three_base_gates
