/-
  Nock/NockVMROM/Thm54/PreZCensusCore.lean

  A pure module-graph refactor (the `PM` `formR-core-lift` pattern): every declaration in §1–§2 is
  moved **verbatim and under its original fully qualified name** from the module named beside it;
  the source modules import this one.

  * **§1 — from `StrategyOfTraces`** (namespace `Nock.NockVMROM.Thm54.StrategyOfTraces`):
    `memoryStateOf`, the memory selector decoder (base columns `0, 1, 2`).
  * `preStateOfEnvs` / `preAtomOfEnvs` (per row), `preLblOfEnvs` / `preFoOfEnvs` /
    `preReqIdxOfEnvs` (1-indexed, row `0` out of range, as `PreSeedCensus.preLbl`),
    `preZNounOfEnvs`, `reqTgtOfEnvs`, `reqPairsOfEnvs`, `reqPairEventOfEnvs` (the `liftSeed`
    cylinder on `JointCoins K`) with `reqPairEventOfEnvs_card_le` (`≤ M·(2Λ − 1)·|𝕂|³`, no
    premise), and `requestTargets` (the root / child noun of the skeleton's `k`-th request,
    `1`-indexed as `RecordCarrier.honestExp`).  Read set: base columns `0, 1, 2` (selectors),
    `180` (`atom`), `181` (`reqIdx`) only.  At `envs := P.memoryBaseEnv Qm` they ARE
    `PreSeedCensus.preZNoun` / `Batch742.reqTgt` / `zipPairs`.
-/
import Nock.NockVMROM.Thm54.HostileSkeletonDecoding
import Nock.NockVMROM.Thm54.JointSoundness
import Nock.Walk
import Nock.NPR
import Nock.GlobalCarryRecognizer
import Nock.NockVMROM.Thm54.RecordCarrier
import Nock.NockVMROM.Thm54.SemanticStrategy
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! ## §1  From `StrategyOfTraces` (verbatim, same name) -/

namespace Nock.NockVMROM.Thm54.StrategyOfTraces

open scoped Classical Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Framework
open Nock.Reified
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-- Base-field selectors of the memory chip. -/
def memoryStateOf (envF : Env F) : MState :=
  if envF.trace 0 = 1 then .decompose
  else if envF.trace 1 = 1 then .halt
  else if envF.trace 2 = 1 then .read_root
  else .verify_child

end

end Nock.NockVMROM.Thm54.StrategyOfTraces

/-! ## §2  From `PreSeedCensus` (verbatim, same names) -/

namespace Nock.NockVMROM.Thm54.PreSeedCensus

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding

noncomputable section

/-- **The pre-`z` decoder**: `decodeNoun`'s shape, with the `halt` leaf read from the committed
`𝔽` atom instead of the `𝕂` leaf column. -/
def decodePre {F : Type} (K : Type) [Field F] [Field K] [Algebra F K] (q : ℕ) :
    NTree (MState × F) → Noun
  | .node (.halt, a) [] => Noun.atom (leafAtomOf q (algebraMap F K a))
  | .node (.decompose, _) [left, right] =>
      Noun.cell (decodePre K q left) (decodePre K q right)
  | .node (.read_root, _) [child] => decodePre K q child
  | .node (.verify_child, _) [child] => decodePre K q child
  | _ => Noun.atom 0

section Bridge

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem decode_node_congr (q : ℕ) (l : MState × DTmem K) (pl : MState × F)
    (hs : l.1 = pl.1)
    (hleaf : pl.1 = .halt →
      leafAtomOf q l.2.2.pt.noun.leaf = leafAtomOf q (algebraMap F K pl.2))
    (cs : List (NTree (MState × DTmem K))) (ds : List (NTree (MState × F)))
    (hcd : List.Forall₂ (fun t u => decodeNoun q t = decodePre K q u) cs ds) :
    decodeNoun q (.node l cs) = decodePre K q (.node pl ds) := by
  obtain ⟨s, d⟩ := l
  obtain ⟨s', a⟩ := pl
  simp only at hs hleaf
  subst hs
  cases s <;>
    rcases hcd with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, hrest⟩⟩⟩ <;>
    simp_all [decodeNoun, decodePre]

/-- **Node-by-node bridge on `Walk.buildTF`.**  Two label maps with the same states and the same
decoded `halt` atoms give the same decoded noun at every position (no tiling premise). -/
theorem decodeNoun_buildTF_eq_decodePre (q kroots hh : ℕ) (fo : ℕ → ℕ)
    (lbl : ℕ → MState × DTmem K) (plbl : ℕ → MState × F)
    (hst : ∀ j, (lbl j).1 = (plbl j).1)
    (hleaf : ∀ j, (plbl j).1 = .halt →
      leafAtomOf q (lbl j).2.2.pt.noun.leaf = leafAtomOf q (algebraMap F K (plbl j).2)) :
    ∀ i, decodeNoun q (buildTF kroots fo lbl hh i) =
      decodePre K q (buildTF kroots fo plbl hh i) := by
  intro i
  induction hm : hh - i using Nat.strong_induction_on generalizing i with
  | _ m ih =>
    rw [buildTF, buildTF]
    refine decode_node_congr q (lbl i) (plbl i) (hst i) (hleaf i) _ _ ?_
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro x _
    have hx := x.2
    simp only [childIdxsF, List.mem_filter, decide_eq_true_eq] at hx
    exact ih (hh - x.1) (by omega) x.1 rfl

end Bridge

section PairEvent

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- **The guard** (standing rule 4b): only pairs whose two nouns both have `≤ Λ` leaves are
priced, which is exactly the premise `NPR.collision_card_le_tight` needs. -/
def guardedPairs (Λ : ℕ) (pairs : List (Noun × Noun)) : List (Noun × Noun) :=
  pairs.filter fun p => decide (p.1.leaves ≤ Λ ∧ p.2.leaves ≤ Λ)

theorem guardedPairs_length_le (Λ : ℕ) (pairs : List (Noun × Noun)) :
    (guardedPairs Λ pairs).length ≤ pairs.length :=
  List.length_filter_le _ _

/-- The guarded pair list as a `ComparisonCensus` (`JointSoundness.lean`). -/
def guardedCensus (Λ : ℕ) (pairs : List (Noun × Noun)) : ComparisonCensus Λ where
  count := (guardedPairs Λ pairs).length
  pair i := (guardedPairs Λ pairs).get i
  leaves_bounded i := by
    have h := List.get_mem (guardedPairs Λ pairs) i
    simp only [guardedPairs, List.mem_filter, decide_eq_true_eq] at h
    exact h.2

/-- **The fixed-pair bad seeds**: the `z` at which some guarded listed pair is field-distinct and
fingerprint-equal (`¬ SepSeed`). -/
def pairBadSeeds (Λ : ℕ) (pairs : List (Noun × Noun)) : Finset K :=
  (guardedCensus Λ pairs).badSeeds (K := K)

/-- **Card `≤ |pairs|·(2Λ − 1)`**: `2Λ − 1` per pair, union over the listed pairs. -/
theorem pairBadSeeds_card_le (Λ : ℕ) (pairs : List (Noun × Noun)) :
    (pairBadSeeds (K := K) Λ pairs).card ≤ pairs.length * (2 * Λ - 1) :=
  le_trans (ComparisonCensus.badSeeds_card_le _)
    (Nat.mul_le_mul_right _ (guardedPairs_length_le Λ pairs))

theorem mem_pairBadSeeds_iff (Λ : ℕ) (pairs : List (Noun × Noun)) (z : K) :
    z ∈ pairBadSeeds Λ pairs ↔
      ∃ p ∈ pairs, p.1.leaves ≤ Λ ∧ p.2.leaves ≤ Λ ∧
        ¬ GlobalCarryRecognizer.SepSeed z p.1 p.2 := by
  unfold pairBadSeeds
  rw [ComparisonCensus.mem_badSeeds_iff]
  constructor
  · rintro ⟨i, hi⟩
    have h := List.get_mem (guardedPairs Λ pairs) i
    simp only [guardedPairs, List.mem_filter, decide_eq_true_eq] at h
    exact ⟨_, h.1, h.2.1, h.2.2, hi⟩
  · rintro ⟨p, hp, h1, h2, hsep⟩
    have hmem : p ∈ guardedPairs Λ pairs := by
      simp only [guardedPairs, List.mem_filter, decide_eq_true_eq]
      exact ⟨hp, h1, h2⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
    refine ⟨i, ?_⟩
    show ¬ GlobalCarryRecognizer.SepSeed z ((guardedPairs Λ pairs).get i).1
      ((guardedPairs Λ pairs).get i).2
    rw [hi]
    exact hsep

/-- A listed, guarded, field-distinct pair colliding at `z` puts `z` in the event (priced). -/
theorem mem_pairBadSeeds_of_collision {Λ : ℕ} {pairs : List (Noun × Noun)} {z : K}
    {d t : Noun} (hmem : (d, t) ∈ pairs) (hd : d.leaves ≤ Λ) (ht : t.leaves ≤ Λ)
    (hdist : (NPR.leafF (K := K) d, NPR.dyckBits (K := K) d)
      ≠ (NPR.leafF (K := K) t, NPR.dyckBits (K := K) t))
    (hfn : NPR.fn d z = NPR.fn t z) :
    z ∈ pairBadSeeds Λ pairs :=
  (mem_pairBadSeeds_iff Λ pairs z).2 ⟨(d, t), hmem, hd, ht, fun hsep => hsep hdist hfn⟩

/-- Outside the event, a listed guarded pair with equal fingerprints is one field-noun. -/
theorem fieldNoun_eq_of_not_mem_pairBadSeeds {Λ : ℕ} {pairs : List (Noun × Noun)} {z : K}
    (hz : z ∉ pairBadSeeds Λ pairs) {d t : Noun} (hmem : (d, t) ∈ pairs)
    (hd : d.leaves ≤ Λ) (ht : t.leaves ≤ Λ)
    (henc : GlobalCarryRecognizer.enc z d = GlobalCarryRecognizer.enc z t) :
    (NPR.leafF (K := K) d, NPR.dyckBits (K := K) d)
      = (NPR.leafF (K := K) t, NPR.dyckBits (K := K) t) := by
  have hsep : GlobalCarryRecognizer.SepSeed z d t := by
    by_contra h
    exact hz ((mem_pairBadSeeds_iff Λ pairs z).2 ⟨(d, t), hmem, hd, ht, h⟩)
  exact GlobalCarryRecognizer.field_noun_eq_of_sepSeed z d t hsep henc

/-- A census of equal pairs (the honest case) prices nothing. -/
theorem pairBadSeeds_eq_empty_of_diag (Λ : ℕ) (pairs : List (Noun × Noun))
    (h : ∀ p ∈ pairs, p.1 = p.2) : pairBadSeeds (K := K) Λ pairs = ∅ := by
  ext z
  simp only [Finset.notMem_empty, iff_false]
  rw [mem_pairBadSeeds_iff]
  rintro ⟨p, hp, -, -, hsep⟩
  apply hsep
  intro hne
  exact absurd (by rw [h p hp]) hne

/-- A distinct pair of naturals below `ringChar K` stays distinct in `K`. -/
theorem natCast_inj_of_lt {a b : ℕ} (ha : a < ringChar K) (hb : b < ringChar K)
    (h : (a : K) = (b : K)) : a = b := by
  have hm := (CharP.natCast_eq_natCast K (ringChar K)).1 h
  unfold Nat.ModEq at hm
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hm

theorem list_eq_of_map_natCast_eq :
    ∀ l₁ l₂ : List ℕ, (∀ k ∈ l₁, k < ringChar K) → (∀ k ∈ l₂, k < ringChar K) →
      l₁.map (fun k : ℕ => (k : K)) = l₂.map (fun k : ℕ => (k : K)) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: l₁, b :: l₂, h₁, h₂, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      have hab := natCast_inj_of_lt (K := K) (h₁ a (by simp)) (h₂ b (by simp)) h.1
      have hl := list_eq_of_map_natCast_eq l₁ l₂ (fun k hk => h₁ k (by simp [hk]))
        (fun k hk => h₂ k (by simp [hk])) h.2
      rw [hab, hl]

/-- **Field-nouns with atoms below the characteristic are nouns**. -/
theorem noun_eq_of_fieldNoun_eq {n₁ n₂ : Noun}
    (h₁ : ∀ k ∈ n₁.leafList, k < ringChar K) (h₂ : ∀ k ∈ n₂.leafList, k < ringChar K)
    (h : (NPR.leafF (K := K) n₁, NPR.dyckBits (K := K) n₁)
      = (NPR.leafF (K := K) n₂, NPR.dyckBits (K := K) n₂)) : n₁ = n₂ := by
  simp only [Prod.mk.injEq, NPR.leafF, NPR.dyckBits] at h
  have hinj : Function.Injective (fun b : Bool => if b then (1 : K) else 0) := by
    intro a b hab
    cases a <;> cases b <;> simp_all
  have hd : n₁.dyckWord = n₂.dyckWord := List.map_injective_iff.mpr hinj h.2
  have hl : n₁.leafList = n₂.leafList := list_eq_of_map_natCast_eq _ _ h₁ h₂ h.1
  exact Noun.noun_dyck_leaf_injective (Prod.ext hd hl)

end PairEvent

/-- Decoded pre-`z` atoms lie below `q`. -/
theorem decodePre_leafList_lt {F : Type} (K : Type) [Field F] [Field K] [Algebra F K]
    {q : ℕ} (hq : 0 < q) (t : NTree (MState × F)) :
    ∀ k ∈ (decodePre K q t).leafList, k < q := by
  induction t using decodePre.induct with
  | case1 a =>
      intro k hk
      simp only [decodePre, Noun.leafList, List.mem_singleton] at hk
      subst hk
      exact leafAtomOf_lt_of_pos hq _
  | case2 _ l r ihl ihr =>
      intro k hk
      simp only [decodePre, Noun.leafList, List.mem_append] at hk
      rcases hk with hk | hk
      · exact ihl k hk
      · exact ihr k hk
  | case3 _ c ih => intro k hk; simp only [decodePre] at hk; exact ih k hk
  | case4 _ c ih => intro k hk; simp only [decodePre] at hk; exact ih k hk
  | case5 t h1 h2 h3 h4 =>
      intro k hk
      rw [decodePre.eq_5 (K := K) (q := q) t h1 h2 h3 h4] at hk
      simp only [Noun.leafList, List.mem_singleton] at hk
      omega


/-! ## §3  New: the env-parametric pre-`z` decoder and the route-B pair event

Every definition below takes the row environments `envs : Fin M → Env F` instead (with
`hM : 0 < M` for the out-of-range row-`0` convention of `preLbl`), and reads only the base columns
`0, 1, 2` (selectors, through `memoryStateOf`), `atomCol = 180` and `reqIdxCol = 181`. -/

section OfEnvs

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {M : ℕ}

/-- Row `i`'s pre-`z` state (selector columns `0, 1, 2`). -/
def preStateOfEnvs (envs : Fin M → Env F) (i : Fin M) : MState :=
  memoryStateOf (envs i)

/-- Row `i`'s committed pre-seed atom (column `atomCol = 180`). -/
def preAtomOfEnvs (envs : Fin M → Env F) (i : Fin M) : F :=
  (envs i).trace atomCol

/-- 1-indexed pre-`z` label (state, atom); out of range reads row `0` (`preLbl`'s convention). -/
def preLblOfEnvs (envs : Fin M → Env F) (hM : 0 < M) (j : ℕ) : MState × F :=
  if hj : j - 1 < M then
    (preStateOfEnvs envs ⟨j - 1, hj⟩, preAtomOfEnvs envs ⟨j - 1, hj⟩)
  else
    (preStateOfEnvs envs ⟨0, hM⟩, preAtomOfEnvs envs ⟨0, hM⟩)

/-- Pre-`z` fanout (`fanoutMem` of the selector state). -/
def preFoOfEnvs (envs : Fin M → Env F) (hM : 0 < M) : ℕ → ℕ :=
  fun j => fanoutMem (preLblOfEnvs envs hM j).1

/-- 1-indexed committed request index (`reqIdxCol = 181`), row `0` out of range. -/
def preReqIdxOfEnvs (envs : Fin M → Env F) (hM : 0 < M) (j : ℕ) : F :=
  if hj : j - 1 < M then (envs ⟨j - 1, hj⟩).trace reqIdxCol
  else (envs ⟨0, hM⟩).trace reqIdxCol

/-- The decoded noun at aggregate-BFS position `i` of the pre-`z` forest of `envs`. -/
def preZNounOfEnvs (K : Type) [Field K] [Algebra F K] (q kroots : ℕ)
    (envs : Fin M → Env F) (hM : 0 < M) (i : ℕ) : Noun :=
  decodePre K q (buildTF kroots (preFoOfEnvs envs hM) (preLblOfEnvs envs hM) M i)

/-- **The route-B target** at position `j`: a fixed map `T` (reads neither trace nor coins) at the
row's pre-`z` state and at `natLift` of its pre-`z` request index. -/
def reqTgtOfEnvs (envs : Fin M → Env F) (hM : 0 < M) (T : MState → ℕ → Noun) : ℕ → Noun :=
  fun j => T (preLblOfEnvs envs hM j).1 (RecordCarrier.natLift (preReqIdxOfEnvs envs hM j))

/-- **The route-B census**: decoded node `i` against `reqTgtOfEnvs … i`, `i = 1..M`. -/
def reqPairsOfEnvs (K : Type) [Field K] [Algebra F K] (q kroots : ℕ)
    (envs : Fin M → Env F) (hM : 0 < M) (T : MState → ℕ → Noun) : List (Noun × Noun) :=
  (List.range' 1 M).map fun i => (preZNounOfEnvs K q kroots envs hM i, reqTgtOfEnvs envs hM T i)

theorem reqPairsOfEnvs_length (K : Type) [Field K] [Algebra F K] (q kroots : ℕ)
    (envs : Fin M → Env F) (hM : 0 < M) (T : MState → ℕ → Noun) :
    (reqPairsOfEnvs K q kroots envs hM T).length = M := by
  simp [reqPairsOfEnvs]

/-- **The route-B pair event** on `JointCoins K`: the `z`-cylinder over the guarded bad seeds of
the route-B census. -/
def reqPairEventOfEnvs (K : Type) [Field K] [Fintype K] [DecidableEq K] [Algebra F K]
    (q kroots Λ : ℕ) (envs : Fin M → Env F) (hM : 0 < M) (T : MState → ℕ → Noun) :
    Finset (JointCoins K) :=
  liftSeed (pairBadSeeds (K := K) Λ (reqPairsOfEnvs K q kroots envs hM T))

/-- **Card `≤ M·(2Λ − 1)·|𝕂|³`** at every `envs` (rule 8(b): no premise; the guard is inside
`pairBadSeeds`). -/
theorem reqPairEventOfEnvs_card_le (K : Type) [Field K] [Fintype K] [DecidableEq K]
    [Algebra F K] (q kroots Λ : ℕ) (envs : Fin M → Env F) (hM : 0 < M)
    (T : MState → ℕ → Noun) :
    (reqPairEventOfEnvs K q kroots Λ envs hM T).card ≤
      M * (2 * Λ - 1) * Fintype.card K ^ 3 := by
  have hB := pairBadSeeds_card_le (K := K) Λ (reqPairsOfEnvs K q kroots envs hM T)
  rw [reqPairsOfEnvs_length] at hB
  rw [reqPairEventOfEnvs, card_liftSeed]
  exact Nat.mul_le_mul_right _ hB

end OfEnvs

/-! ### `requestTargets`: the skeleton's request nouns, indexed by exponent -/

/-- The skeleton's request list: compute rows in BFS order, each row's active records in slot
order (`recordCount`), i.e. the order in which the timestamps' exponents `S(i) + j + 1` count. -/
def requestList (S : SemanticStrategy.SemanticSkeleton) : List SemanticStrategy.MemRecSkeleton :=
  (SemanticStrategy.computeSkeletonRows S).flatMap fun r =>
    (List.finRange 3).filterMap fun (i : Fin 3) =>
      if h : (i : ℕ) < Nock.Framework.recordCount r.state then some (r.memoryRecord i h) else none

/-- **`requestTargets S st k`**: the root noun (`read_root`) / child noun (`verify_child`) of the
skeleton's `k`-th request (`1`-indexed, as `RecordCarrier.honestExp`); `atom 0` for `k = 0`, past
the end, and at every other state.  Fixed by the skeleton: reads neither trace nor coins. -/
def requestTargets (S : SemanticStrategy.SemanticSkeleton) : MState → ℕ → Noun
  | .read_root, k + 1 => ((requestList S)[k]?.map SemanticStrategy.MemRecSkeleton.root).getD (.atom 0)
  | .verify_child, k + 1 =>
      ((requestList S)[k]?.map SemanticStrategy.MemRecSkeleton.child).getD (.atom 0)
  | _, _ => .atom 0

end

end Nock.NockVMROM.Thm54.PreSeedCensus
