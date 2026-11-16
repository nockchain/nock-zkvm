/-
  Nock/NockVMROM/Thm54/PreSeedCensus.lean

  **The pre-`z` census and the fixed-pair event (`≤ 2Λ − 1` per pair).  NOT CONSUMED.**

  * **The pre-`z` read model.**  `PreZAgreeOn cc Q Q'`: `Q`, `Q'` agree on
    every column whose declared challenge set `cc` excludes `z` (`zIdx`, the landed tuple's
    coordinate 3).  `PreZReads V S` for a staged view `V` (`DeployedStaging.StagedRAPView`) uses
    `V.columnChallenges` as the column → coin map (`PI` F1 repair, `Batch622.b1_challenge_sets`).
  * **`preSeedCensus`**: the multiset of `halt` atoms, read off the selector
    and `atom` columns only (`preSeedCensus_preZReads`).  `preZNoun` decodes every BFS node of the
    pre-`z` forest (selectors give the shape, `atom` gives the leaves).
  * **§3 — the accepted-trace bridge.**  On every trace accepted at `memoryChipAt c`, the decoder's
    noun at every node of the committed forest IS the pre-`z` noun
    (`accepted_decode_eq_preZNoun`): the `halt` gate (`decodeMemPub_halt_leaf_eq_atom`) makes the
    round-1 leaf read equal to the round-0 `atom` read, and everything else the decoder reads is
    the selectors.  No walk-tiling premise: it is stated node by node on `Walk.buildTF`.
  * **The pair event.**  `pairEvent P q Λ Qm tgt` lifts it on `z` over the
    positional census `zipPairs` (decoded node `i` ↔ fixed target `tgt i`, `|pairs| = M`).
    Cylinder: membership reads only the `z` coordinate (`mem_pairEvent_iff`) and only the pre-`z`
    columns of `Qm` (`pairEvent_preZReads`); a strategy that fixes the round-0 columns and chooses
    the rest after `z` meets the same fixed set (`pairEvent_adaptive_eq`).  Card
    `≤ M·(2Λ − 1)·|𝕂|¹⁰` (`pairEvent_card_le`).  The all-pairs census `crossPairs`
    (`≤ M·|tgts|`, `≤ M²` when `|tgts| ≤ M`) is the worst case.
  * **The conjunct**, beside the statement: on an accepted trace outside the
    event, a decoded node whose fingerprint at `z` equals its target's (the binding the consumer
    must supply) IS the target (`accepted_outside_pairEvent_decoded_eq`).

  **Commitment-order premise (brief step 3, `PF` F1 / `PI` F1).**  `RAP.Satisfies` ignores rounds,
  and the capstone fixes ALL of `Qc, Qm` before the challenge tuple (`OptimizedFalseAcceptanceSet
  Qc Qm` is a filter of `Finset.univ` over tuples at fixed traces).  The census needs strictly less:
  only the memory round-0 columns `0, 1, 2, 180` fixed before `z`.  The event is defined on that
  same basis (a filter of `Finset.univ` at fixed `Qm`, `pairEvent_basis`), so it slots into the
  capstone's own count (`failure_union_pairEvent_card_le`), and it does not degrade in a staged
  model where later columns are chosen after `z` (`pairEvent_adaptive_eq`).
-/
import Nock.NockVMROM.Thm54.MemoryHaltAtomDecode
import Nock.NockVMROM.Thm54.DeployedStaging
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.NockVMROM.Thm54.PreZCensusCore
import Nock.NockVMROM.Thm54.P8Core.PreSeedCensus
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

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
open Nock.NockVMROM.Thm54.DeployedStaging
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.MemoryHaltAtomDecode
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding

noncomputable section

/-! ## The pre-`z` read model over `DeployedStaging.columnChallenges` -/

/-- `z` as a coordinate of the deployed chronology (`FormRAxisEvent.seedIdx`, landed index `3`). -/
def zIdx : Fin deployedChronology.numChallenges := FormRAxisEvent.seedIdx

/-- `z` is sampled after round `0`. -/
theorem zIdx_sampledAfter : ((deployedChronology.sampledAfter zIdx : Fin 3) : ℕ) = 0 := rfl

/-- A round-`r` column may read `z` iff `r ≠ 0`. -/
theorem zIdx_mem_roundChallenges_iff (r : Fin 3) :
    zIdx ∈ roundChallenges r ↔ (r : ℕ) ≠ 0 := by
  simp only [roundChallenges, Finset.mem_filter, Finset.mem_univ, true_and, zIdx_sampledAfter]
  omega

section Generic

variable {ι α : Type*}

/-- Two column assignments agree on every column whose declared challenge set excludes `z`. -/
def PreZAgreeOn (cc : ι → Finset (Fin deployedChronology.numChallenges)) (Q Q' : ι → α) : Prop :=
  ∀ c, zIdx ∉ cc c → Q c = Q' c

/-- A function of the columns reads only pre-`z` data. -/
def PreZReadsFnOn {β : Sort*} (cc : ι → Finset (Fin deployedChronology.numChallenges))
    (f : (ι → α) → β) : Prop :=
  ∀ Q Q', PreZAgreeOn cc Q Q' → f Q = f Q'

variable {F : Type*} [Field F]

/-- **`PreZReads V S`**: membership of a column tuple in `S` depends only on the columns whose
`V.columnChallenges` exclude `z`. -/
def PreZReads (V : StagedRAPView F 3 deployedChronology) (S : Set (Fin V.width → α)) : Prop :=
  ∀ Q Q', PreZAgreeOn V.columnChallenges Q Q' → (Q ∈ S ↔ Q' ∈ S)

/-- A set that reads only a set `D` of `z`-free columns is `PreZReads`. -/
theorem preZReads_of_readsOnly (V : StagedRAPView F 3 deployedChronology)
    (D : Finset (Fin V.width)) (hD : ∀ c ∈ D, zIdx ∉ V.columnChallenges c)
    (S : Set (Fin V.width → α))
    (hS : ∀ Q Q' : Fin V.width → α, (∀ c ∈ D, Q c = Q' c) → (Q ∈ S ↔ Q' ∈ S)) :
    PreZReads V S :=
  fun Q Q' hag => hS Q Q' fun c hc => hag c (hD c hc)

/-- A pair of pre-`z`-agreeing tuples separated by `S` refutes `PreZReads`. -/
theorem not_preZReads_of_witness (V : StagedRAPView F 3 deployedChronology)
    (S : Set (Fin V.width → α)) (Q Q' : Fin V.width → α)
    (hag : PreZAgreeOn V.columnChallenges Q Q') (hQ : Q ∈ S) (hQ' : Q' ∉ S) :
    ¬ PreZReads V S :=
  fun h => hQ' ((h Q Q' hag).1 hQ)

end Generic

section DeployedMemory

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Module.Basis (Fin 3) F K)
  (chalVal pubVal : ℕ → F) (orbit : StrictExtension.StrictOrbitDomain F 3 h) (kMem : ℕ)

/-- **At the deployed memory view, a column reads no `z` iff its B1 round is `0`.** -/
theorem memView_preZ_iff (c : Fin 205) :
    zIdx ∉ (deployedMemoryView hn nodes b chalVal pubVal orbit kMem).columnChallenges c ↔
      memoryColRound c = 0 := by
  show zIdx ∉ roundChallenges (memoryRoundFin c) ↔ _
  rw [zIdx_mem_roundChallenges_iff]
  simp [memoryRoundFin]

end DeployedMemory

/-! ## `preSeedCensus` and the pre-`z` forest -/

section Production

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- `DeployedStaging`'s column → coin map, read on the package's memory trace columns. -/
def memCC (col : Fin P.memoryChip.rap.w) : Finset (Fin deployedChronology.numChallenges) :=
  (memView P).columnChallenges (Fin.cast (memView P).hw col)

theorem memCC_preZ_iff (col : Fin P.memoryChip.rap.w) :
    zIdx ∉ memCC P col ↔ memoryColRound col.val = 0 :=
  memView_preZ_iff _ _ _ _ _ _ _ (Fin.cast (memView P).hw col)

/-- **The trace read is pre-`z` on every round-0 column.** -/
theorem preEnv_trace_congr {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (hag : PreZAgreeOn (memCC P) Qm Qm') (i : Fin P.optimized.family.problem.cfg.memRows)
    (j : ℕ) (hj : memoryColRound j = 0) :
    (preEnv P Qm i).trace j = (preEnv P Qm' i).trace j := by
  simp only [preEnv, OptimizedFullStrictNockVMROMPackage.memoryBaseEnv, envOfTrace]
  split_ifs with hlt
  · congr 1
    simp only [OptimizedFullStrictNockVMROMPackage.memorySourceTrace, RAPPadding.projectTrace]
    exact hag _ ((memCC_preZ_iff P _).2 hj)
  · rfl

theorem preState_congr {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (hag : PreZAgreeOn (memCC P) Qm Qm') (i : Fin P.optimized.family.problem.cfg.memRows) :
    preState P Qm i = preState P Qm' i := by
  have h0 := preEnv_trace_congr P hag i 0 (by decide)
  have h1 := preEnv_trace_congr P hag i 1 (by decide)
  have h2 := preEnv_trace_congr P hag i 2 (by decide)
  simp only [preState, memoryStateOf, h0, h1, h2]

theorem preAtom_congr {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (hag : PreZAgreeOn (memCC P) Qm Qm') (i : Fin P.optimized.family.problem.cfg.memRows) :
    preAtom P Qm i = preAtom P Qm' i :=
  preEnv_trace_congr P hag i atomCol (by decide)

theorem preLbl_congr {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (hag : PreZAgreeOn (memCC P) Qm Qm') : preLbl P Qm = preLbl P Qm' := by
  funext j
  unfold preLbl
  split_ifs <;> rw [preState_congr P hag, preAtom_congr P hag]

theorem preFo_congr {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (hag : PreZAgreeOn (memCC P) Qm Qm') : preFo P Qm = preFo P Qm' := by
  unfold preFo; rw [preLbl_congr P hag]

end Production

section Production2

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The pre-`z` decoded nouns, one per committed memory row (BFS positions `1..M`). -/
def preZNouns (q : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X]) : List Noun :=
  (List.range' 1 P.optimized.family.problem.cfg.memRows).map (preZNoun P q Qm)

/-- **`preSeedCensus`** (brief step 4): the multiset of decoded `halt` atoms, read off the selector
and `atom` columns only. -/
def preSeedCensus (q : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X]) : Multiset ℕ :=
  (((List.finRange P.optimized.family.problem.cfg.memRows).filter
      (fun i => preState P Qm i = .halt)).map
    (fun i => leafAtomOf q (algebraMap F K (preAtom P Qm i))) : Multiset ℕ)

/-- **The census is a function of pre-`z` data only.** -/
theorem preSeedCensus_preZReads (q : ℕ) :
    PreZReadsFnOn (memCC P) (preSeedCensus P q) := by
  intro Qm Qm' hag
  unfold preSeedCensus
  congr 1
  have hs : ∀ i, preState P Qm i = preState P Qm' i := preState_congr P hag
  have ha : ∀ i, preAtom P Qm i = preAtom P Qm' i := preAtom_congr P hag
  simp only [hs, ha]

theorem preZNoun_preZReads (q : ℕ) (i : ℕ) :
    PreZReadsFnOn (memCC P) (fun Qm => preZNoun P q Qm i) := by
  intro Qm Qm' hag
  simp only [preZNoun, preLbl_congr P hag, preFo_congr P hag]

theorem preZNouns_preZReads (q : ℕ) :
    PreZReadsFnOn (memCC P) (preZNouns P q) := by
  intro Qm Qm' hag
  have h : preZNoun P q Qm = preZNoun P q Qm' :=
    funext fun i => preZNoun_preZReads P q i Qm Qm' hag
  simp only [preZNouns, h]

/-- Every census entry is a decoded `halt` atom of some row. -/
theorem mem_preSeedCensus_iff (q : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X]) (k : ℕ) :
    k ∈ preSeedCensus P q Qm ↔
      ∃ i, preState P Qm i = .halt ∧ leafAtomOf q (algebraMap F K (preAtom P Qm i)) = k := by
  simp [preSeedCensus]

end Production2

/-! ## §3  The accepted-trace bridge: decoded nouns are pre-`z` nouns -/

section Bridge

variable {F K : Type} [Field F] [Field K] [Algebra F K]

variable [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The same at the roots of the committed forest (`reconForest`, as `execOfTraces` builds it). -/
theorem accepted_decodedRoots_eq_preZ (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm) (q : ℕ) :
    (reconForest P.optimized.family.problem.cfg.kMem (foM P (honestQm P c Qm) c)
        (lblM P (honestQm P c Qm) c) P.optimized.family.problem.cfg.memRows).map
          (decodeNoun q) =
      (List.range' 1 P.optimized.family.problem.cfg.kMem).map
        (preZNoun P q (honestQm P c Qm)) := by
  simp only [reconForest, List.map_map]
  apply List.map_congr_left
  intro i _
  exact accepted_decode_eq_preZNoun P c Qm hsat q i

/-- **Step 4 ↔ decoder**: an accepted `halt` row's decoded atom is a census entry. -/
theorem accepted_halt_atom_mem_census (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm) (q : ℕ)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hst : (decodeMemPub P (honestQm P c Qm) c i).st = .halt) :
    ∃ k ∈ preSeedCensus P q (honestQm P c Qm),
      decodeNoun q (.node (lblMAt P (honestQm P c Qm) c i) []) = Noun.atom k := by
  refine ⟨_, (mem_preSeedCensus_iff P q _ _).2 ⟨i, hst, rfl⟩, ?_⟩
  exact decodeNoun_halt_eq_atom P c Qm hsat q i hst

end Bridge

/-! ## The fixed-pair event over the census -/

section ProductionEvent

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem preZNoun_leafList_lt {q : ℕ} (hq : 0 < q) (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : ℕ) : ∀ k ∈ (preZNoun P q Qm i).leafList, k < q :=
  decodePre_leafList_lt K hq _

/-- **The positional census**: decoded node `i` against its fixed target `tgt i` (the skeleton's /
claim's noun at BFS position `i`; `tgt` reads neither the trace nor the coins).  `|pairs| = M`. -/
def zipPairs (q : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X]) (tgt : ℕ → Noun) :
    List (Noun × Noun) :=
  (List.range' 1 P.optimized.family.problem.cfg.memRows).map fun i => (preZNoun P q Qm i, tgt i)

theorem zipPairs_length (q : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X]) (tgt : ℕ → Noun) :
    (zipPairs P q Qm tgt).length = P.optimized.family.problem.cfg.memRows := by
  simp [zipPairs]

theorem zipPairs_preZReads (q : ℕ) (tgt : ℕ → Noun) :
    PreZReadsFnOn (memCC P) (fun Qm => zipPairs P q Qm tgt) := by
  intro Qm Qm' hag
  have h : preZNoun P q Qm = preZNoun P q Qm' :=
    funext fun i => preZNoun_preZReads P q i Qm Qm' hag
  simp only [zipPairs, h]

/-- **The all-pairs census** (worst case): every decoded node against every listed target. -/
def crossPairs (q : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X]) (tgts : List Noun) :
    List (Noun × Noun) :=
  (preZNouns P q Qm).flatMap fun d => tgts.map fun t => (d, t)

theorem crossPairs_length (q : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X]) (tgts : List Noun) :
    (crossPairs P q Qm tgts).length = P.optimized.family.problem.cfg.memRows * tgts.length := by
  simp [crossPairs, preZNouns, List.length_flatMap, Function.comp_def, List.map_const',
    List.sum_replicate]

/-- `M²` when the targets are at most one per memory row. -/
theorem crossPairs_badSeeds_card_le_sq (q Λ : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X])
    (tgts : List Noun) (ht : tgts.length ≤ P.optimized.family.problem.cfg.memRows) :
    (pairBadSeeds (K := K) Λ (crossPairs P q Qm tgts)).card ≤
      P.optimized.family.problem.cfg.memRows * P.optimized.family.problem.cfg.memRows *
        (2 * Λ - 1) := by
  refine le_trans (pairBadSeeds_card_le Λ _) (Nat.mul_le_mul_right _ ?_)
  rw [crossPairs_length]
  exact Nat.mul_le_mul_left _ ht

/-- **The fixed-pair event, lifted on `z`** over the positional census. -/
def pairEvent (q Λ : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X]) (tgt : ℕ → Noun) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.filter fun c => nprSeed c.1 ∈ pairBadSeeds (K := K) Λ (zipPairs P q Qm tgt)

/-- **Cylinder, coin side**: membership reads only the `z` coordinate of the landed tuple. -/
theorem mem_pairEvent_iff (q Λ : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X]) (tgt : ℕ → Noun)
    (c : OptimizedProductionChallengeTuple K F) :
    c ∈ pairEvent P q Λ Qm tgt ↔
      FormRAxisEvent.landedVec c FormRAxisEvent.seedIdx ∈
        pairBadSeeds (K := K) Λ (zipPairs P q Qm tgt) := by
  simp only [pairEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem pairEvent_readsOnly_z (q Λ : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X]) (tgt : ℕ → Noun)
    (c c' : OptimizedProductionChallengeTuple K F)
    (h : FormRAxisEvent.landedVec c FormRAxisEvent.seedIdx =
      FormRAxisEvent.landedVec c' FormRAxisEvent.seedIdx) :
    c ∈ pairEvent P q Λ Qm tgt ↔ c' ∈ pairEvent P q Λ Qm tgt := by
  rw [mem_pairEvent_iff, mem_pairEvent_iff, h]

/-- `z` is the first coin: no coordinate of the landed tuple is sampled before it, so the bad set
over `z` may read no coin at all (`ReadsOn ∅`), which `pairBadSeeds` does not. -/
theorem seed_prior_empty :
    RoundFibred.priorCoords FormRAxisEvent.landedRound FormRAxisEvent.seedIdx = ∅ := by
  decide

/-- **Cylinder, trace side**: the event reads only the pre-`z` columns of `Qm`. -/
theorem pairEvent_preZReads (q Λ : ℕ) (tgt : ℕ → Noun) :
    PreZReadsFnOn (memCC P) (fun Qm => pairEvent (K := K) P q Λ Qm tgt) := by
  intro Qm Qm' hag
  simp only [pairEvent, zipPairs_preZReads P q tgt Qm Qm' hag]

/-- **Staged model**: a prover that fixes the round-0 columns as `Qm₀` and chooses every other
column after seeing the coins meets the same fixed event. -/
theorem pairEvent_adaptive_eq (q Λ : ℕ) (tgt : ℕ → Noun) (Qm₀ : Fin P.memoryChip.rap.w → F[X])
    (σ : OptimizedProductionChallengeTuple K F → Fin P.memoryChip.rap.w → F[X])
    (hσ : ∀ c, PreZAgreeOn (memCC P) (σ c) Qm₀) :
    Finset.univ.filter (fun c => nprSeed c.1 ∈ pairBadSeeds (K := K) Λ (zipPairs P q (σ c) tgt))
      = pairEvent P q Λ Qm₀ tgt := by
  ext c
  simp only [pairEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    zipPairs_preZReads P q tgt (σ c) Qm₀ (hσ c)]

/-- The event is the `liftSeed` cylinder, lifted to the production tuple. -/
theorem pairEvent_eq_lift (q Λ : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X]) (tgt : ℕ → Noun) :
    pairEvent P q Λ Qm tgt =
      liftP8Failure (F := F) (liftSeed (pairBadSeeds (K := K) Λ (zipPairs P q Qm tgt))) := by
  ext c
  simp [pairEvent, liftP8Failure, mem_liftSeed_iff]

/-- **Card `≤ M·(2Λ − 1)·|𝕂|¹⁰`** of the `|𝕂|¹¹` tuples, i.e. `≤ M·(2Λ − 1)/|𝕂|`. -/
theorem pairEvent_card_le (q Λ : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X]) (tgt : ℕ → Noun) :
    (pairEvent P q Λ Qm tgt).card ≤
      P.optimized.family.problem.cfg.memRows * (2 * Λ - 1) * Fintype.card K ^ 10 := by
  have hB := pairBadSeeds_card_le (K := K) Λ (zipPairs P q Qm tgt)
  rw [zipPairs_length] at hB
  rw [pairEvent_eq_lift]
  simp only [liftP8Failure, Finset.card_product, Finset.card_univ, card_liftSeed,
    Fintype.card_prod, card_finalComputeChallengeTuple, card_memoryChallengeTuple]
  calc (pairBadSeeds (K := K) Λ (zipPairs P q Qm tgt)).card * Fintype.card K ^ 3 *
        (Fintype.card K * Fintype.card K * (Fintype.card K ^ 3 * Fintype.card K ^ 2))
      = (pairBadSeeds (K := K) Λ (zipPairs P q Qm tgt)).card * Fintype.card K ^ 10 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hB

theorem failure_union_pairEvent_card_le (q Λ : ℕ) (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) (tgt : ℕ → Noun) :
    (P.optimizedFailureEvent Qc Qm ∪ pairEvent P q Λ Qm tgt).card ≤
      (P.optimizedFailureEvent Qc Qm).card +
        P.optimized.family.problem.cfg.memRows * (2 * Λ - 1) * Fintype.card K ^ 10 :=
  le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left (pairEvent_card_le P q Λ Qm tgt) _)

/-- And so the capstone's false-acceptance set, at the same fixed traces, sits in that union. -/
theorem falseAcceptance_subset_union (q Λ : ℕ)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) (tgt : ℕ → Noun) :
    P.OptimizedFalseAcceptanceSet Qc Qm ⊆
      P.consumedFailureEvent Qc Qm ∪ pairEvent P q Λ Qm tgt :=
  (P.optimizedFalseAcceptanceSet_subset_failure hax hbasis hwidth Qc Qm).trans
    Finset.subset_union_left

/-! ## The conjunct, beside the consumed statement -/

/-- **The conjunct.**  On a trace accepted at `memoryChipAt c`, with `c` outside the pair event:
every decoded forest node whose fingerprint at `z` equals its fixed target's (`hbind`, the binding
the consumer supplies) and that sits in the window `Λ` IS that target.  Not in the statement. -/
theorem accepted_outside_pairEvent_decoded_eq (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    {q Λ : ℕ} (hq0 : 0 < q) (hqp : q ≤ ringChar K) (tgt : ℕ → Noun)
    (hout : c ∉ pairEvent P q Λ (honestQm P c Qm) tgt)
    {i : ℕ} (hi : i ∈ List.range' 1 P.optimized.family.problem.cfg.memRows)
    (hwin : (preZNoun P q (honestQm P c Qm) i).leaves ≤ Λ) (htwin : (tgt i).leaves ≤ Λ)
    (htgt : ∀ k ∈ (tgt i).leafList, k < q)
    (hbind : GlobalCarryRecognizer.enc (nprSeed c.1)
        (decodeNoun q (buildTF P.optimized.family.problem.cfg.kMem (foM P (honestQm P c Qm) c)
          (lblM P (honestQm P c Qm) c) P.optimized.family.problem.cfg.memRows i)) =
      GlobalCarryRecognizer.enc (nprSeed c.1) (tgt i)) :
    decodeNoun q (buildTF P.optimized.family.problem.cfg.kMem (foM P (honestQm P c Qm) c)
        (lblM P (honestQm P c Qm) c) P.optimized.family.problem.cfg.memRows i) = tgt i := by
  rw [accepted_decode_eq_preZNoun P c Qm hsat q i] at hbind ⊢
  have hz : nprSeed c.1 ∉ pairBadSeeds (K := K) Λ (zipPairs P q (honestQm P c Qm) tgt) := by
    intro h
    exact hout (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  have hmem : (preZNoun P q (honestQm P c Qm) i, tgt i) ∈ zipPairs P q (honestQm P c Qm) tgt :=
    List.mem_map.2 ⟨i, hi, rfl⟩
  have hfield := fieldNoun_eq_of_not_mem_pairBadSeeds hz hmem hwin htwin hbind
  exact noun_eq_of_fieldNoun_eq
    (fun k hk => lt_of_lt_of_le (preZNoun_leafList_lt P hq0 _ i k hk) hqp)
    (fun k hk => lt_of_lt_of_le (htgt k hk) hqp) hfield

/-- The same for every node at once: the decoded forest equals the target forest. -/
theorem accepted_outside_pairEvent_forest_eq (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    {q Λ : ℕ} (hq0 : 0 < q) (hqp : q ≤ ringChar K) (tgt : ℕ → Noun)
    (hout : c ∉ pairEvent P q Λ (honestQm P c Qm) tgt)
    (hwin : ∀ i ∈ List.range' 1 P.optimized.family.problem.cfg.memRows,
      (preZNoun P q (honestQm P c Qm) i).leaves ≤ Λ ∧ (tgt i).leaves ≤ Λ ∧
        ∀ k ∈ (tgt i).leafList, k < q)
    (hbind : ∀ i ∈ List.range' 1 P.optimized.family.problem.cfg.memRows,
      GlobalCarryRecognizer.enc (nprSeed c.1)
        (decodeNoun q (buildTF P.optimized.family.problem.cfg.kMem (foM P (honestQm P c Qm) c)
          (lblM P (honestQm P c Qm) c) P.optimized.family.problem.cfg.memRows i)) =
      GlobalCarryRecognizer.enc (nprSeed c.1) (tgt i)) :
    (List.range' 1 P.optimized.family.problem.cfg.memRows).map
        (fun i => decodeNoun q (buildTF P.optimized.family.problem.cfg.kMem
          (foM P (honestQm P c Qm) c) (lblM P (honestQm P c Qm) c)
          P.optimized.family.problem.cfg.memRows i)) =
      (List.range' 1 P.optimized.family.problem.cfg.memRows).map tgt := by
  apply List.map_congr_left
  intro i hi
  exact accepted_outside_pairEvent_decoded_eq P c Qm hsat hq0 hqp tgt hout hi
    (hwin i hi).1 (hwin i hi).2.1 (hwin i hi).2.2 (hbind i hi)

/-- **Receipt: the honest case lies outside.**  When every decoded node is its target (an honest
trace's forest is the skeleton's), the event is empty. -/
theorem pairEvent_eq_empty_of_decoded_eq (q Λ : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X])
    (tgt : ℕ → Noun)
    (h : ∀ i ∈ List.range' 1 P.optimized.family.problem.cfg.memRows, preZNoun P q Qm i = tgt i) :
    pairEvent (K := K) P q Λ Qm tgt = ∅ := by
  have hdiag : ∀ p ∈ zipPairs P q Qm tgt, p.1 = p.2 := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
    exact h i hi
  ext c
  simp [pairEvent, pairBadSeeds_eq_empty_of_diag Λ _ hdiag]

end ProductionEvent

end

end Nock.NockVMROM.Thm54.PreSeedCensus
