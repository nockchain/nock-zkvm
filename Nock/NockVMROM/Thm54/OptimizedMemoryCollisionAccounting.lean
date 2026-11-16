import Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
import Nock.NockVMROM.Thm54.OptimizedMemoryConcrete

/-!
# Collision accounting for the disjoint memory partition

Before the merge it was `82 - 21 = 61`. The four selector
equalities and three base scalar compressions contribute seven independent degree-two scalar
families, hence fourteen additional scalar roots; the merge does not touch them. -/

namespace Nock.NockVMROM.Thm54
namespace OptimizedMemoryCollisionAccounting

open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Module
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateBasis
open OptimizedComputeCollisionBound
open OptimizedMemoryGateBasis
open OptimizedMemoryCanonicalSatisfaction

noncomputable section

noncomputable local instance : Fintype ConcreteStrictPackage.K73cubic :=
  Fintype.ofFinite ConcreteStrictPackage.K73cubic
noncomputable local instance : DecidableEq ConcreteStrictPackage.K73cubic :=
  Classical.decEq ConcreteStrictPackage.K73cubic
local instance : CharP ConcreteStrictPackage.K73cubic 73 := inferInstance
local instance : CharP ConcreteStrictPackage.K73cubic
    (ringChar ConcreteStrictPackage.K73cubic) :=
  ringChar.charP ConcreteStrictPackage.K73cubic

def extensionFoldFamily {K : Type} [Field K] (j : Fin 21) : List Expr :=
  if hj : (j : ℕ) < 19 then
    [extensionFoldSources (K := K).get ⟨j, by
       have hlen : (extensionFoldSources (K := K)).length = 40 := extensionFoldSources_length
       omega⟩,
     extensionFoldSources (K := K).get ⟨(j : ℕ) + 21, by
       have hlen : (extensionFoldSources (K := K)).length = 40 := extensionFoldSources_length
       omega⟩]
  else
    [extensionFoldSources (K := K).get ⟨j, by
       have hlen : (extensionFoldSources (K := K)).length = 40 := extensionFoldSources_length
       omega⟩]

/-- Carrier-indexed fold partition.  List lengths do not depend on `K`. -/
def extensionFoldFamiliesOf {K : Type} [Field K] : List (List Expr) :=
  List.ofFn (extensionFoldFamily (K := K))

/-- Same lengths at every carrier. -/
def extensionFoldFamilies : List (List Expr) :=
  extensionFoldFamiliesOf (K := ConcreteStrictPackage.K73cubic)

/-- **The merged fold workload: `19`.**  `40 = 21 · 1 + 19`, so nineteen buckets are degree-one
in the fold challenge and two are degree-zero: `19 · 1 + 2 · 0 = 19`. -/
theorem extensionFoldFamily_length {K : Type} [Field K] (j : Fin 21) :
    (extensionFoldFamily (K := K) j).length = if (j : ℕ) < 19 then 2 else 1 := by
  rw [extensionFoldFamily]
  split <;> rfl

theorem extensionFoldFamiliesOf_workload {K : Type} [Field K] :
    ((extensionFoldFamiliesOf (K := K)).map fun es => es.length - 1).sum = 19 := by
  rw [extensionFoldFamiliesOf, List.map_ofFn]
  unfold Function.comp
  simp only [extensionFoldFamily_length]
  decide

theorem extensionFoldFamilies_workload :
    (extensionFoldFamilies.map fun (es : List Expr) => es.length - 1).sum = 19 :=
  extensionFoldFamiliesOf_workload (K := ConcreteStrictPackage.K73cubic)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
theorem extensionFoldFamily_polynomial_eval
    {K : Type} [Field K] (env : Env K) (j : Fin 21) :
    (finalRlcPolynomial env (extensionFoldFamily (K := K) j)).eval (foldChallenge.eval env) =
      (foldAt (K := K) j).eval env := by
  fin_cases j <;>
    simp [extensionFoldFamily, extensionFoldSources, sourceIndices, finalRlcPolynomial,
      foldAt, foldChallenge, Expr.eval] <;>
    ring_nf

theorem extensionFoldSource_mem_family
    {K : Type} [Field K]
    (j : Fin 21) (i : Fin (extensionFoldSources (K := K)).length)
    (hi : (i : ℕ) % 21 = j) :
    extensionFoldSources (K := K).get i ∈ extensionFoldFamily (K := K) j := by
  have hlen : (extensionFoldSources (K := K)).length = 40 := extensionFoldSources_length
  have hdiv := Nat.mod_add_div (i : ℕ) 21
  have hq : (i : ℕ) / 21 ≤ 1 := by omega
  interval_cases hqi : (i : ℕ) / 21
  · have hieq : i = ⟨j, by omega⟩ := Fin.ext (by simp; omega)
    rw [hieq]
    rw [extensionFoldFamily]
    split <;> exact List.mem_cons_self
  · have hj : (j : ℕ) < 19 := by omega
    have hieq : i = ⟨(j : ℕ) + 21, by omega⟩ := Fin.ext (by simp; omega)
    rw [hieq]
    rw [extensionFoldFamily, dif_pos hj]
    exact List.mem_cons_of_mem _ List.mem_cons_self

def extensionFoldBadChallenges
    {K : Type} [Field K] [Fintype K] [DecidableEq K] (env : Env K) : Finset K :=
  badChallengesFor env (extensionFoldFamiliesOf (K := K))


theorem extensionFoldBadChallenges_card_le_19
    {K : Type} [Field K] [Fintype K] [DecidableEq K] (env : Env K) :
    (extensionFoldBadChallenges env).card ≤ 19 := by
  calc
    (extensionFoldBadChallenges env).card ≤
        (extensionFoldFamiliesOf (K := K).map fun es => es.length - 1).sum :=
      badChallengesFor_card_le env (extensionFoldFamiliesOf (K := K))
    _ = 19 := extensionFoldFamiliesOf_workload

/-- The pre-merge bound, retained with slack: every statement priced at `61` stays true. -/
theorem extensionFoldBadChallenges_card_le_61
    {K : Type} [Field K] [Fintype K] [DecidableEq K] (env : Env K) :
    (extensionFoldBadChallenges env).card ≤ 61 :=
  (extensionFoldBadChallenges_card_le_19 env).trans (by omega)

theorem foldCollisionExcluded_of_not_bad
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (env : Env K)
    (hgood : foldChallenge.eval env ∉ extensionFoldBadChallenges env) :
    FoldCollisionExcluded env := by
  intro j hfold i hi
  by_contra hsource
  apply hgood
  apply mem_badChallengesFor_of env (extensionFoldFamiliesOf (K := K))
    (extensionFoldFamily (K := K) j)
  · exact List.mem_ofFn.mpr ⟨j, rfl⟩
  · exact ⟨extensionFoldSources (K := K).get i, by
      exact extensionFoldSource_mem_family j i hi,
      hsource⟩
  · rw [extensionFoldFamily_polynomial_eval env j, hfold]

def scalarCompressionBadChallenges
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (families : List (List F)) : Finset F :=
  families.foldr (fun es acc => valueBadChallenges es ∪ acc) ∅

theorem scalarCompressionBadChallenges_card_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (families : List (List F)) :
    (scalarCompressionBadChallenges families).card ≤
      (families.map fun es => es.length - 1).sum := by
  induction families with
  | nil => simp [scalarCompressionBadChallenges]
  | cons es families ih =>
      simp only [scalarCompressionBadChallenges, List.foldr_cons, List.map_cons, List.sum_cons]
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add (valueBadChallenges_card_le es) ih)

theorem seven_scalar_families_card_le_14
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (families : Fin 7 → Fin 3 → F) :
    (scalarCompressionBadChallenges
      (List.ofFn fun i : Fin 7 => List.ofFn (families i))).card ≤ 14 := by
  calc
    _ ≤ ((List.ofFn fun i : Fin 7 => List.ofFn (families i)).map
        fun es => es.length - 1).sum :=
      scalarCompressionBadChallenges_card_le _
    _ = 14 := by simp

/-- Exact two-space collision accounting for one row: 19 extension-field roots and
14 independent base-field roots. -/
theorem repaired_memory_collision_union_bounds
    {F : Type*} {K : Type} [Field F] [Fintype F] [DecidableEq F]
    [Field K] [Fintype K] [DecidableEq K]
    (envK : Env K) (families : Fin 7 → Fin 3 → F) :
    (extensionFoldBadChallenges envK).card ≤ 19 ∧
      (scalarCompressionBadChallenges
        (List.ofFn fun i : Fin 7 => List.ofFn (families i))).card ≤ 14 :=
  ⟨extensionFoldBadChallenges_card_le_19 envK,
    seven_scalar_families_card_le_14 families⟩

/-! ## All-row product-space accounting

The definitions below preserve the exact
allocation: challenge 6 in `K`, selector challenge 0 in `F`, and the first-mask, last-mask, and
chain challenges 1, 2, and 3 in `F`. Every coordinate is shared across all rows. -/

/-- **The memory chip's challenge tuple: the internal `intermediate` LogUp pole.**

W4 stage 2 (Design A): one extra `𝕂` element versus the paper.  The coordinate is the
memory table's internal pole (the paper `RLC^γ(mem_record) − β`); the record-RLC coin `γ`
is reused from sampled IO `γ` (slot `4`).  Slot `6` of `memoryChallengeTargets` carries this
value (it was the dead fold `I.memoryExtensionFold` after W2 stage 3).

It carried `extensionFold : 𝕂` until W2 stage 3, then was the unit type until this insertion.
It carried four further base-field coordinates — `selectorEquality`, `firstMask`, `lastMask`,
`chain : 𝔽` — until stage 3d.  The product shape `c.2.2.1` / `c.2.2.2` of
`OptimizedProductionChallengeTuple` is stable. -/
@[ext]
structure MemoryChallengeTuple (K : Type*) where
  interPole : K
  /-- Accounting base `λ`.  Same round as `α`.
      Chip slots: `memoryKOfTuple 8`, `computeKOfTuple 9`. -- the paper -/
  lambda : K
deriving DecidableEq, Fintype

theorem memoryChallengeTuple_card
    (K : Type*) [Fintype K] :
    Fintype.card (MemoryChallengeTuple K) = Fintype.card K ^ 2 := by
  let e : MemoryChallengeTuple K ≃ (K × K) :=
    { toFun := fun c => (c.interPole, c.lambda)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := by intro c; cases c; rfl
      right_inv := by intro p; rfl }
  rw [Fintype.card_congr e]
  simp [pow_two]

def allMemoryExtensionBadChallenges
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {M : ℕ} (envK : Fin M → Env K) : Finset K :=
  Finset.univ.biUnion fun i => extensionFoldBadChallenges (envK i)

def allMemoryScalarBadChallenges
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {M : ℕ} (families : Fin M → Fin 7 → Fin 3 → F) : Finset F :=
  Finset.univ.biUnion fun i =>
    scalarCompressionBadChallenges
      (List.ofFn fun j : Fin 7 => List.ofFn (families i j))

def allMemoryScalarBadChallengesAt
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {M : ℕ} (families : Fin M → Fin 7 → Fin 3 → F) (j : Fin 7) : Finset F :=
  Finset.univ.biUnion fun i => valueBadChallenges (List.ofFn (families i j))

def allMemorySelectorBadChallenges
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {M : ℕ} (families : Fin M → Fin 7 → Fin 3 → F) : Finset F :=
  Finset.univ.biUnion fun j : Fin 4 =>
    allMemoryScalarBadChallengesAt families ⟨j, by omega⟩


theorem allMemoryExtensionBadChallenges_card_le_19
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {M : ℕ} (envK : Fin M → Env K) :
    (allMemoryExtensionBadChallenges envK).card ≤ 19 * M := by
  calc
    (allMemoryExtensionBadChallenges envK).card
        ≤ ∑ i : Fin M, (extensionFoldBadChallenges (envK i)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin M, 19 :=
      Finset.sum_le_sum fun i _ => extensionFoldBadChallenges_card_le_19 (envK i)
    _ = 19 * M := by simp [Nat.mul_comm]

/-- The pre-merge all-row bound, retained with slack. -/
theorem allMemoryExtensionBadChallenges_card_le
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {M : ℕ} (envK : Fin M → Env K) :
    (allMemoryExtensionBadChallenges envK).card ≤ 61 * M :=
  (allMemoryExtensionBadChallenges_card_le_19 envK).trans (by omega)

theorem allMemoryScalarBadChallenges_card_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {M : ℕ} (families : Fin M → Fin 7 → Fin 3 → F) :
    (allMemoryScalarBadChallenges families).card ≤ 14 * M := by
  calc
    (allMemoryScalarBadChallenges families).card
        ≤ ∑ i : Fin M,
            (scalarCompressionBadChallenges
              (List.ofFn fun j : Fin 7 => List.ofFn (families i j))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin M, 14 :=
      Finset.sum_le_sum fun i _ => seven_scalar_families_card_le_14 (families i)
    _ = 14 * M := by simp [Nat.mul_comm]

theorem allMemoryScalarBadChallengesAt_card_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {M : ℕ} (families : Fin M → Fin 7 → Fin 3 → F) (j : Fin 7) :
    (allMemoryScalarBadChallengesAt families j).card ≤ 2 * M := by
  calc
    _ ≤ ∑ i : Fin M, (valueBadChallenges (List.ofFn (families i j))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin M, 2 := Finset.sum_le_sum fun i _ =>
      (valueBadChallenges_card_le (List.ofFn (families i j))).trans_eq (by simp)
    _ = 2 * M := by simp [Nat.mul_comm]

theorem allMemorySelectorBadChallenges_card_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {M : ℕ} (families : Fin M → Fin 7 → Fin 3 → F) :
    (allMemorySelectorBadChallenges families).card ≤ 8 * M := by
  calc
    _ ≤ ∑ j : Fin 4,
        (allMemoryScalarBadChallengesAt families ⟨j, by omega⟩).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin 4, 2 * M := Finset.sum_le_sum fun j _ =>
      allMemoryScalarBadChallengesAt_card_le families ⟨j, by omega⟩
    _ = 8 * M := by simp; ring

/-- Lift a bad-pole set as a **cylinder** over `lambda`.  Membership still reads `interPole ∈ bad`. -/
def liftMemoryExtension
    {K : Type*} [Fintype K] [DecidableEq K]
    (bad : Finset K) : Finset (MemoryChallengeTuple K) :=
  (bad ×ˢ (Finset.univ : Finset K)).map
    ⟨fun p => ⟨p.1, p.2⟩, by
      intro a b h
      apply Prod.ext
      · exact congrArg MemoryChallengeTuple.interPole h
      · exact congrArg MemoryChallengeTuple.lambda h⟩

@[simp] theorem mem_liftMemoryExtension
    {K : Type*} [Fintype K] [DecidableEq K]
    (bad : Finset K) (c : MemoryChallengeTuple K) :
    c ∈ liftMemoryExtension bad ↔ c.interPole ∈ bad := by
  simp [liftMemoryExtension, MemoryChallengeTuple.ext_iff]
  constructor
  · rintro ⟨a, ha, x, h1, -⟩
    exact (show a = c.interPole from h1) ▸ ha
  · intro h
    exact ⟨c.interPole, h, c.lambda, rfl, rfl⟩

@[simp] theorem liftMemoryExtension_card
    {K : Type*} [Fintype K] [DecidableEq K] (bad : Finset K) :
    (liftMemoryExtension bad).card = bad.card * Fintype.card K := by
  rw [liftMemoryExtension, Finset.card_map, Finset.card_product, Finset.card_univ]

/-! ## The extension-only memory event

**The four base-field lifts were not merely unused: they priced gates that are not committed.**
The compressed gates `firstMaskBindingGate`, `lastMaskBindingGate`, `intermediateChainGate` and
`selectorEquality` are in **neither** deployed list —
`GatheredMemoryScalarGates.the_four_scalar_gates_are_retyped` puts `baseTransitionGates` at `11`
and `equalityChecks` at `12`, all of them coordinates of the `𝕂`-valued mixed forms — and
`MixedMemoryGates.repaired_good_from_committed_buckets_and_fold` reassembles the whole of
`RepairedMemoryCollisionGood` from the chip's own committed gates plus the fold exclusion, with
no selector, mask or chain coin in its hypotheses.  So the corresponding `14 · M / |𝔽|` charge is
**slack**, and the consumed memory event shrinks to its one extension-field lift.

**Stage 3d removed the four base-field coordinates themselves**, so
`fullMemoryCollisionEvent`, its four scalar lifts, `FullMemoryCollisionGood` and the bridge
`extensionMemoryCollisionEvent_subset_full` are gone: none of them is statable over a tuple that
has no such coordinate. The `19 · M / |𝕂|` price and every theorem that consumes it are
unchanged. -/

/-- W2 stage 3: the fold coin is gone, so the memory collision event is empty.
Previously inhabited as the one-lift image. -/
def extensionMemoryCollisionEvent
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {M : ℕ} (_envK : Fin M → Env K) :
    Finset (MemoryChallengeTuple K) :=
  ∅

def ExtensionMemoryCollisionGood
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {M : ℕ} (envK : Fin M → Env K) (c : MemoryChallengeTuple K) : Prop :=
  c ∉ extensionMemoryCollisionEvent envK

/-- Vacuous since W2 stage 3: the event is empty.  Previously stated as `19 · M`. -/
theorem extensionMemoryCollisionEvent_card_le
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {M : ℕ} (envK : Fin M → Env K) :
    (extensionMemoryCollisionEvent envK).card ≤ 19 * M := by
  simp [extensionMemoryCollisionEvent]

/-- Vacuous since W2 stage 3: the event is empty, so every tuple is good.  Previously stated with
`19 · M < |𝕂|`. -/
theorem exists_extensionMemoryCollisionGood_of_bound_lt
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {M : ℕ} (envK : Fin M → Env K)
    (_hlt : 19 * M < Fintype.card K) :
    ∃ c : MemoryChallengeTuple K, ExtensionMemoryCollisionGood envK c :=
  ⟨⟨0, 0⟩, by simp [ExtensionMemoryCollisionGood, extensionMemoryCollisionEvent]⟩

/-- W2 stage 3
deleted the coordinate; the event is empty and the pin is gone. -/
theorem foldCollisionExcluded_of_extension_good
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {M : ℕ} (envK : Fin M → Env K) (c : MemoryChallengeTuple K)
    (_hgood : ExtensionMemoryCollisionGood envK c) :
    True :=
  trivial

/-- The event is empty, so the
quotient is 0; the bound is retained as a (now slack) majorant. -/
def extensionMemoryCollisionProbabilityBound
    (K : Type*) [Fintype K] (M : ℕ) : ℚ :=
  (19 * M : ℚ) / Fintype.card K

theorem extensionMemoryCollisionProbability_le
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {M : ℕ} (envK : Fin M → Env K) :
    ((extensionMemoryCollisionEvent envK).card : ℚ) / (Fintype.card K) ≤
      extensionMemoryCollisionProbabilityBound K M := by
  have hcast : ((extensionMemoryCollisionEvent envK).card : ℚ) ≤ ((19 * M : ℕ) : ℚ) := by
    exact_mod_cast extensionMemoryCollisionEvent_card_le envK
  have hk : (0 : ℚ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  calc
    ((extensionMemoryCollisionEvent envK).card : ℚ) / (Fintype.card K)
        ≤ (((19 * M : ℕ)) : ℚ) / (Fintype.card K) :=
      div_le_div_of_nonneg_right hcast (by positivity)
    _ = extensionMemoryCollisionProbabilityBound K M := by
      simp only [extensionMemoryCollisionProbabilityBound, Nat.cast_mul, Nat.cast_ofNat]


def RepairedMemoryCollisionGood
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (envF : Env F) (envK : Env K) : Prop :=
  FoldCollisionExcluded envK ∧
  FirstMaskCollisionExcluded b envF ∧
  LastMaskCollisionExcluded b envF ∧
  ChainCollisionExcluded envF ∧
  SelectorEqualityCollisionExcluded b envF

def RepairedMemoryCollisionEvent
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (envF : Env F) (envK : Env K) : Prop :=
  ¬ RepairedMemoryCollisionGood b envF envK

def selectorEqualityCoord
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (s : Fin 4) (k : Fin 3) : CoeffExpr F :=
  CoeffExpr.sub
    (CoeffExpr.var .traceCur (6 + 3 * (51 + s) + k))
    (CoeffExpr.mul (CoeffExpr.const (coord b (1 : K) k))
      (CoeffExpr.var .traceCur s))

def repairedMemoryScalarFamilies
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (env : Env F) : Fin 7 → Fin 3 → F
  | ⟨j, _hj⟩, k =>
      if hsel : j < 4 then
        (selectorEqualityCoord b ⟨j, hsel⟩ k).eval env
      else if j = 4 then (maskBindingCoord b 47 4 k).eval env
      else if j = 5 then (maskBindingCoord b 48 5 k).eval env
      else (chainCoord k).eval env

def ValueCollisionExcluded {F : Type*} [Field F] (ρ : F) (as : List F) : Prop :=
  (valueRlcPolynomial as).eval ρ = 0 → ∀ a ∈ as, a = 0

theorem mem_badChallengesFor_iff
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (env : Env K) (families : List (List Expr)) (z : K) :
    z ∈ badChallengesFor env families ↔
      ∃ es ∈ families, (∃ e ∈ es, e.eval env ≠ 0) ∧
        (finalRlcPolynomial env es).eval z = 0 := by
  induction families with
  | nil => simp [badChallengesFor]
  | cons es families ih =>
      by_cases hnz : ∃ e ∈ es, e.eval env ≠ 0
      · rw [badChallengesFor, List.foldr_cons, if_pos hnz,
          Finset.mem_union]
        change z ∈ familyBadChallenges env es ∨ z ∈ badChallengesFor env families ↔ _
        rw [ih]
        simp only [familyBadChallenges, Finset.mem_filter, Finset.mem_univ,
          true_and, List.mem_cons]
        constructor
        · rintro (hroot | ⟨qs, hqs, hqsnz, hqsroot⟩)
          · exact ⟨es, Or.inl rfl, hnz, hroot⟩
          · exact ⟨qs, Or.inr hqs, hqsnz, hqsroot⟩
        · rintro ⟨qs, rfl | hqs, hqsnz, hroot⟩
          · exact Or.inl hroot
          · exact Or.inr ⟨qs, hqs, hqsnz, hroot⟩
      · rw [badChallengesFor, List.foldr_cons, if_neg hnz]
        change z ∈ badChallengesFor env families ↔ _
        rw [ih]
        simp only [List.mem_cons]
        constructor
        · rintro ⟨qs, hqs, hqsnz, hroot⟩
          exact ⟨qs, Or.inr hqs, hqsnz, hroot⟩
        · rintro ⟨qs, rfl | hqs, hqsnz, hroot⟩
          · exact (hnz hqsnz).elim
          · exact ⟨qs, hqs, hqsnz, hroot⟩

theorem mem_valueBadChallenges_iff
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (as : List F) (ρ : F) :
    ρ ∈ valueBadChallenges as ↔
      (∃ a ∈ as, a ≠ 0) ∧ (valueRlcPolynomial as).eval ρ = 0 := by
  by_cases hnz : ∃ a ∈ as, a ≠ 0
  · simp [valueBadChallenges, hnz]
  · simp [valueBadChallenges, hnz]

theorem extensionFold_not_bad_of_collision_excluded
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (env : Env K) (z : K) (hpin : foldChallenge.eval env = z)
    (hfree : FoldCollisionExcluded env) :
    z ∉ extensionFoldBadChallenges env := by
  intro hbad
  obtain ⟨es, hes, ⟨e, he, hene⟩, hroot⟩ :=
    (mem_badChallengesFor_iff env (extensionFoldFamiliesOf (K := K)) z).1 hbad
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hes
  have hfold : (foldAt (K := K) j).eval env = 0 := by
    have hpoly := extensionFoldFamily_polynomial_eval env j
    rw [hpin] at hpoly
    exact hpoly.symm.trans hroot
  have hezero : e.eval env = 0 := by
    have hlen : (extensionFoldSources (K := K)).length = 40 := extensionFoldSources_length
    rw [extensionFoldFamily] at he
    split at he
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact hfree j hfold ⟨j, by omega⟩ (by simp)
      · exact hfree j hfold ⟨(j : ℕ) + 21, by omega⟩ (by
          simpa [Nat.add_mod] using j.isLt)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      subst he
      exact hfree j hfold ⟨j, by omega⟩ (by simp)
  exact hene hezero

/-- Vacuous since W2 stage 3: the event is empty.  Previously stated with the fold pin and
row-wise `FoldCollisionExcluded`. -/
theorem extensionMemoryCollisionGood_of_fold_excluded
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {M : ℕ} (envK : Fin M → Env K) (c : MemoryChallengeTuple K)
    (_hfold : ∀ i, FoldCollisionExcluded (envK i)) :
    ExtensionMemoryCollisionGood envK c := by
  simp [ExtensionMemoryCollisionGood, extensionMemoryCollisionEvent]

theorem value_not_bad_of_collision_excluded
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ρ : F) (as : List F) (hfree : ValueCollisionExcluded ρ as) :
    ρ ∉ valueBadChallenges as := by
  intro hbad
  obtain ⟨⟨a, ha, hane⟩, hroot⟩ := (mem_valueBadChallenges_iff as ρ).1 hbad
  exact hane (hfree hroot a ha)

theorem valueCollisionExcluded_of_not_bad
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ρ : F) (as : List F) (hgood : ρ ∉ valueBadChallenges as) :
    ValueCollisionExcluded ρ as := by
  intro hpoly a ha
  by_contra hne
  have hnonzero : ∃ x ∈ as, x ≠ 0 := ⟨a, ha, hne⟩
  apply hgood
  simp [valueBadChallenges, hnonzero, hpoly]

theorem firstMaskPolynomial_eval
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (env : Env F) :
    (valueRlcPolynomial
      (List.ofFn fun k : Fin 3 => (maskBindingCoord b 47 4 k).eval env)).eval
        (env.chal 1) =
      (firstMaskBindingGate b).eval env := by
  simp [valueRlcPolynomial, firstMaskBindingGate, rlc3, CoeffExpr.sumList,
    List.finRange, firstMaskBindingChallenge, CoeffExpr.eval]
  ring

theorem lastMaskPolynomial_eval
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (env : Env F) :
    (valueRlcPolynomial
      (List.ofFn fun k : Fin 3 => (maskBindingCoord b 48 5 k).eval env)).eval
        (env.chal 2) =
      (lastMaskBindingGate b).eval env := by
  simp [valueRlcPolynomial, lastMaskBindingGate, rlc3, CoeffExpr.sumList,
    List.finRange, lastMaskBindingChallenge, CoeffExpr.eval]
  ring

theorem chainPolynomial_eval
    {F : Type} [Field F] (env : Env F) :
    (valueRlcPolynomial
      (List.ofFn fun k : Fin 3 => (chainCoord k).eval env)).eval (env.chal 3) =
      intermediateChainGate.eval env := by
  simp [valueRlcPolynomial, intermediateChainGate, rlc3, CoeffExpr.sumList,
    List.finRange, chainBindingChallenge, CoeffExpr.eval]
  ring

theorem selectorEqualityPolynomial_eval
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (env : Env F) (s : Fin 4) :
    (valueRlcPolynomial
      (List.ofFn fun k : Fin 3 => (selectorEqualityCoord b s k).eval env)).eval
        (env.chal 0) =
      (selectorEquality b s).eval env := by
  simp [valueRlcPolynomial, selectorEquality, selectorEqualityCoord,
    CoeffExpr.sumList, List.finRange, selectorEqualityChallenge, CoeffExpr.eval]
  ring

/-! ### Removed at stage 3d

`fullMemoryCollisionGood_components`, `repairedMemoryCollisionGood_of_full` and
`fullMemoryCollisionGood_of_repaired` all quantified over the four base-field coordinates of
`MemoryChallengeTuple` and are not statable now that it has one coordinate. Their job — getting
`RepairedMemoryCollisionGood` for every row — is done by
`MixedMemoryGates.repaired_good_from_committed_buckets_and_fold`, which takes the chip's own
committed mixed gate buckets plus `foldCollisionExcluded_of_extension_good` and needs no
selector, mask or chain coin at all. -/


theorem mask_and_selector_binding_of_collision_good
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (envF : Env F) (envK : Env K)
    (hgood : RepairedMemoryCollisionGood b envF envK)
    (hfirst : (firstMaskBindingGate b).eval envF = 0)
    (hlast : (lastMaskBindingGate b).eval envF = 0)
    (hselector : ∀ s : Fin 4, (selectorEquality b s).eval envF = 0) :
    (∀ k : Fin 3, (maskBindingCoord b 47 4 k).eval envF = 0) ∧
    (∀ k : Fin 3, (maskBindingCoord b 48 5 k).eval envF = 0) ∧
    (∀ s : Fin 4, ∀ k : Fin 3,
      (CoeffExpr.sub
        (CoeffExpr.var .traceCur (6 + 3 * (51 + s) + k))
        (CoeffExpr.mul (CoeffExpr.const (coord b (1 : K) ⟨k, by omega⟩))
          (CoeffExpr.var .traceCur s))).eval envF = 0) := by
  exact ⟨hgood.2.1 hfirst, hgood.2.2.1 hlast,
    fun s => hgood.2.2.2.2 s (hselector s)⟩

theorem honest_memory_collision_good
    (i : Fin ConcreteStrictPackage.honestLegacyFamily.problem.cfg.memRows) :
    RepairedMemoryCollisionGood ConcreteStrictPackage.basis73
      (OptimizedMemoryCanonicalSatisfaction.canonicalPhysicalEnv
        OptimizedComputeSampledTrace.Concrete.honestSampled
        OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryNodes
        ConcreteStrictPackage.basis73
        OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryChalVal
        OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryPubVal
        ConcreteStrictPackage.strictOrbit i)
      (OptimizedMemoryCanonicalSatisfaction.canonicalGatheredEnv
        OptimizedComputeSampledTrace.Concrete.honestSampled
        OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryNodes
        ConcreteStrictPackage.basis73
        OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryChalVal
        OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryPubVal
        ConcreteStrictPackage.strictOrbit i) := by
  set envK :=
    OptimizedMemoryCanonicalSatisfaction.canonicalGatheredEnv
      OptimizedComputeSampledTrace.Concrete.honestSampled
      OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryNodes
      ConcreteStrictPackage.basis73
      OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryChalVal
      OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryPubVal
      ConcreteStrictPackage.strictOrbit i
  refine ⟨foldCollisionExcluded_of_nonagg envK ?rest ?chal, ?scalar⟩
  · intro e he h23 h24
    exact OptimizedMemoryCanonicalSatisfaction.canonical_transitionSources
      OptimizedComputeSampledTrace.Concrete.honestSampled
      OptimizedMemorySameExecution.Concrete.honestProduction
      ConcreteStrictPackage.honestLegacyFamily.problem.memory_same_lambda
      OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryNodes
      OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryNodes_injective
      ConcreteStrictPackage.basis73
      OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryChalVal
      OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryPubVal
      ConcreteStrictPackage.strictOrbit
      OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryPins
      OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryNodes_aligned
      OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryDenominatorsSafe i
      e (extensionFoldSources_subset_transitionSources e he) h23 h24
  · have hpin :
        foldChallenge.eval envK = (2 : ConcreteStrictPackage.K73cubic) :=
      OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryPins.sampledInterPole
    rw [hpin]
    exact OptimizedMemoryCanonicalSatisfaction.Concrete.honest_two_ne_zero
  exact OptimizedMemoryCanonicalSatisfaction.canonical_scalarCollisionExcluded
    OptimizedComputeSampledTrace.Concrete.honestSampled
    OptimizedMemorySameExecution.Concrete.honestProduction
    OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryNodes
    OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryNodes_injective
    ConcreteStrictPackage.basis73
    OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryChalVal
    OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryPubVal
    ConcreteStrictPackage.strictOrbit
    OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryNodes_aligned i

def scalarCancellationValues : List ℚ := [1, -1, 0]

theorem scalar_compression_cancellation_witness :
    (valueRlcPolynomial scalarCancellationValues).eval 1 = 0 ∧
      (∃ x ∈ scalarCancellationValues, x ≠ 0) ∧
      ¬ ValueCollisionExcluded 1 scalarCancellationValues := by
  norm_num [scalarCancellationValues, valueRlcPolynomial, ValueCollisionExcluded]

/-- All selectors
and challenges are zero; only sampled multiplicity role 39 is malformed. -/
def memoryFoldCancellationEnv : Env ℚ where
  trace i := if i = 30 then 1 else if i = 39 then 2 else 0
  traceNext := fun _ => 0
  chal i := if i = 0 then 1 else 0
  pub := fun _ => 0

theorem memoryFoldCancellation_source_nonzero :
    (sampledSources.get ⟨1, by decide⟩).eval memoryFoldCancellationEnv = 2 := by
  norm_num [sampledSources, extVar, Expr.eval, memoryFoldCancellationEnv]

theorem memoryFoldCancellation_source_mem :
    sampledSources.get ⟨1, by decide⟩ ∈ extensionFoldSources (K := ℚ) := by
  simp [extensionFoldSources, sampledFoldSources]

theorem foldAt_zero_of_zero_challenge_and_first_block
    {K : Type} [Field K] (env : Env K)
    (hchal : env.chal 6 = 0)
    (hfirst : ∀ i : Fin (extensionFoldSources (K := K)).length, (i : ℕ) < 21 →
      (extensionFoldSources (K := K).get i).eval env = 0)
    (j : Fin 21) :
    (foldAt (K := K) j).eval env = 0 := by
  unfold foldAt
  induction sourceIndices (K := K) with
  | nil => simp [Expr.eval]
  | cons i t ih =>
      simp only [List.foldr_cons]
      by_cases hj : (i : ℕ) % 21 = j
      · rw [if_pos hj]
        simp only [Expr.eval, foldChallenge, hchal]
        by_cases hi : (i : ℕ) < 21
        · rw [hfirst i hi, mul_zero, zero_add]
          exact ih
        · have hpow : 0 < (i : ℕ) / 21 := Nat.div_pos (by omega) (by omega)
          rw [zero_pow (Nat.ne_of_gt hpow), zero_mul, zero_add]
          exact ih
      · rw [if_neg hj]
        exact ih

def firstBlockIndex (q : Fin 21) : Fin (extensionFoldSources (K := ℚ)).length :=
  ⟨q, by rw [extensionFoldSources_length]; omega⟩

/-- Every source of the first block vanishes here.  Index `0` is the `z · zinv = 1` witness;
indices `1..20` are merged quantity classes, and every merged gate is a selector-weighted sum
whose four selector roles are zero in this environment. -/
theorem memoryFoldCancellation_first_block_index_zero (q : Fin 21) :
    (extensionFoldSources (K := ℚ).get (firstBlockIndex q)).eval memoryFoldCancellationEnv = 0 := by
  have hsel : ∀ c : ℕ,
      ((MemoryFactorizationScope.mergedGate c).subst memorySubst).eval
        memoryFoldCancellationEnv = 0 := fun c =>
    mergedGate_subst_eval_zero_of_selectors_zero memoryFoldCancellationEnv
      (by norm_num [memoryFoldCancellationEnv]) (by norm_num [memoryFoldCancellationEnv])
      (by norm_num [memoryFoldCancellationEnv]) (by norm_num [memoryFoldCancellationEnv]) c
  fin_cases q
  · norm_num [firstBlockIndex, extensionFoldSources, memoryRowSources,
      mergedMemoryConstraints, memSvExprs, memSvBoolExprs, memSvOneHotExpr, zZinvExprM,
      allMStates, memorySubst, Reified.chl, Reified.tc, extVar,
      Expr.subst, Expr.eval, memoryFoldCancellationEnv]
  · exact hsel 0
  · exact hsel 1
  · exact hsel 2
  · exact hsel 20
  · exact hsel 16
  · exact hsel 5
  · exact hsel 6
  · exact hsel 7
  · exact hsel 8
  · exact hsel 9
  · exact hsel 10
  · exact hsel 11
  · exact hsel 12
  · exact hsel 13
  · exact hsel 14
  · exact hsel 15
  · exact hsel 4
  · exact hsel 17
  · exact hsel 18
  · exact hsel 19

theorem memoryFoldCancellation_first_block_zero :
    ∀ i : Fin (extensionFoldSources (K := ℚ)).length, (i : ℕ) < 21 →
      (extensionFoldSources (K := ℚ).get i).eval memoryFoldCancellationEnv = 0 := by
  intro i hi
  let q : Fin 21 := ⟨i, hi⟩
  have hie : i = firstBlockIndex q := Fin.ext rfl
  rw [hie]
  exact memoryFoldCancellation_first_block_index_zero q

theorem memory_fold_cancellation_witness :
    (∀ g ∈ extensionTransitionGates (K := ℚ), g.eval memoryFoldCancellationEnv = 0) ∧
      (∃ e ∈ extensionFoldSources (K := ℚ), e.eval memoryFoldCancellationEnv ≠ 0) ∧
      ¬ FoldCollisionExcluded memoryFoldCancellationEnv := by
  have hfold : ∀ g ∈ extensionTransitionGates (K := ℚ),
      g.eval memoryFoldCancellationEnv = 0 := by
    intro g hg
    obtain ⟨j, -, rfl⟩ := List.mem_ofFn.mp hg
    apply foldAt_zero_of_zero_challenge_and_first_block
    · rfl
    · exact memoryFoldCancellation_first_block_zero
  refine ⟨hfold, ⟨sampledSources.get ⟨1, by decide⟩,
    memoryFoldCancellation_source_mem, ?_⟩, ?_⟩
  · rw [memoryFoldCancellation_source_nonzero]
    norm_num
  · intro hcollision
    have hz := fold_to_source_of_collision_excluded memoryFoldCancellationEnv hfold hcollision
      (sampledSources.get ⟨1, by decide⟩) memoryFoldCancellation_source_mem
    rw [memoryFoldCancellation_source_nonzero] at hz
    norm_num at hz

end
end OptimizedMemoryCollisionAccounting
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting.repaired_memory_collision_union_bounds
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting.extensionMemoryCollisionEvent_card_le
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting.foldCollisionExcluded_of_extension_good
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting.memory_fold_cancellation_witness
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting.honest_memory_collision_good
