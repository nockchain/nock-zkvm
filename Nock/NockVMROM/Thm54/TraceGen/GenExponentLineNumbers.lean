/-
  Nock/NockVMROM/Thm54/TraceGen/GenExponentLineNumbers.lean

  **The committed timestamp exponent IS a compute-table line number — on the generated path.**

  the paper (re-read at source): "Note that this timestamp is unique and represents the line
  number of the compute table at which the memory record was requested, thus having the closed form
  `z^i ∈ 𝕂`, where `i` is the compute table line number."  The mechanism is
  `Algorithm:NockCompute`'s multiplicative line chain, the paper: `mem_record₁`'s
  timestamp is `ln_prev · z` (`:1728`), `mem_record₂`'s is `ln_prev · z²` (`:1731`),
  `mem_record₃`'s is `ln = ln_prev · z³` (`:1734`, `:1737-1738`), and `ln` advances by `z`, `z²`
  or `z³` according to how many records the row opened (`:1734,1737,1739,1741,1742`); absent
  records are `(0,0,0,0)`.  the paper types the `ln` column ("the number of nodes resolved
  until now") and the paper puts `ln_prev`, `ln`, `mem_record_{1,2,3}` in `W_comp`.

  So the exponent is not free: it is `lnPrevExponent + i + 1`, a line number.

  ## Scope — read this before quoting anything below

  **The identification is FALSE for a general `ProductionStrategy`** (or a general `Data E`):
  `ForestExponentWindow.wrapDataExponents` adds `orderOf α` to every committed exponent and
  produces a different commitment of the *same* execution.  Nothing here claims otherwise.

  * **§A** — `stampOfAcc` (`Gen.lean:763`): every record slot of a stamped row lies in that row's
    own line window `(acc, acc + recordCount st]`.  `∀ state`, `∀ acc`, `∀ i : Fin 3`; **generated
    scope**, because the object is the generator's stamping function.
  * **§B** — `bfsAssign` / `accAt` / `bfsStamps`: the accumulator at the end of BFS *is*
    `ForestExponentWindow.totalRecordCount` of the committed compute rows (the paper's `L`), and
    every exponent `extractNodeReqs` hands to the memory side is `≤ L` with **no slack**.
    `∀` compute tree, `∀ K`; **generated scope**.
  * **§C** — the served forest: `≤ L` for every committed memory-row stamp of
    `genMemForestFromTree`, and the same after `threadGenForest`, i.e. on the *committed*
    `genMemoryForest`.  The induction through the annotated builders is
    `GenSemanticLmIO.genMemForestFromTree_exp_le`, reused at `N = L`; nothing is rebuilt.
    `∀ E z α inp`, `∀` compute tree; **generated scope**.
  * **§D** — two bridges that **assume** a bound and prove nothing about it:
    `committedExponentWindow_of_maxTemplateRecordExponent` is `∀ T : ProductionStrategy F K`;
    `maxTemplateRecordExponent_executionTemplate`, `data_maxTemplateRecordExponent_le`,
    `packageOf_committedTemplate_all_seeds` and `packageOf_committedExponentWindow` are
    `∀ D : Data E`.
  * **§E** — the payoff.  `CommittedExponentWindow` at `B = L`, `fixedAxisWorkload_le` and
    `workload_le_explicit` with no named residual.  **Generated scope**, carried by the explicit
    hypothesis `hmem : D.memoryNodes = genMemoryNodes z α inp t`.
  * **§F** — the same at `Nock.Field.K`; the only section that touches `goldilocks_prime`.
  * **§G** — a *negative* result about `ForestExponentWindow.forestExponentOrder_of_line_numbers`:
    its `hmemLine` premise is refuted by any one zero-exponent committed memory row, and every
    generated served record tree publishes one.  `∀`-generic.
  * **§H** — the paper's sentence as an equality of lists: the committed *request* exponents of a
    generated trace are exactly `1, …, L`.  **Generated scope**, `∀` compute tree.

  Every headline is `#check`ed and `#print axioms`ed at the bottom.  No theorem in §A–§C or §G–§H
  takes a hypothesis fixing a program, a state, an axis, a seed, a field or a field size; §E's only
  such hypothesis is `hmem`, which *is* the generated scope, made visible on purpose.

  Worth writing down because it is easy to guess wrong:

  * `renderNode` (`Gen.lean:2884`) rewrites `ServiceReq.ts` for **all** eleven states with the
    *same* value `α ^ g.stamp.recordExponent 0`.  The per-record `mr1/mr2/mr3.ts` are set inside
    `renderOp*Row z α g.stamp g.skel`, not by `renderNode` itself.  `renderRows` copies `stamp`
    unchanged, so the committed Nat exponents of `genComputeRows` are `bfsAssign`'s.
  * The **committed** served forest is `genMemForestFromTree (encC z) z α (bfsAssign (airReorder t))`
    then `threadGenForest` (`GenSemanticDataParts.lean:43`).  It is built *directly* from
    `extractNodeReqs`, i.e. from `getRecordExp g.stamp i`.  `BFSAssign.memJoinForest` /
    `genJoinedTimestampSkeleton` — the "restamp memory rows from the request slots" pass — are
    **not** on that path: nothing outside `BFSAssign.lean` mentions them.  So the identification is
    a *construction* fact about `extractNodeReqs`, not a matching fact about a restamping pass.
  * `memoryMemRecKind` is `.active` for `read_root` **and** `verify_child`
    (`NounRealization.lean:144`), so both of the states that contribute exponents to
    `readExps`/`verifyExps` are live; the `decompose`/`halt` noun-walk rows are the padding, and
    they are stamped `0`.  That last point is what §G is about.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenWorkloadBounds
import Nock.NockVMROM.Thm54.TraceGen.GenHonestData
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticLmIO
import Nock.NockVMROM.Thm54.GenericHonestPackage

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.ForestExponentWindow

/-! ## §A. `stampOfAcc` puts every record exponent inside the row's own line window

`stampOfAcc st acc` is the generator's stamping function (`Gen.lean:763`).  the paper
gives the row's records the lines `ln_prev·z`, `ln_prev·z²`, `ln_prev·z³`, i.e. the exponents
`acc+1, acc+2, acc+3`, and advances `ln` to `acc + recordCount st`.  Two consequences, both
unconditional in the state and the accumulator (no program, no fixture):

* the *live* exponents are exactly `acc + i + 1` (`Gen.stampOfAcc_recordExponent`, already in the
  tree), and
* **every** slot — live or padding — lands in `(acc, acc + recordCount st]`, so no slot can
  escape the row's own line window.  This second fact is what the served-memory forest needs,
  because `getRecordExp` reads slots by list position and `recordCount` is not visible there. -/

section StampWindow

variable {K : Type} [Field K]

variable {lmb : K}

/-- Every `stampOfAcc` record slot is at least the next line, `acc + 1` (the paper,
`mem_record₁` at `ln_prev·z`; the paper, `ln(1) = α`). -/
theorem stampOfAcc_lt_recordExponent (st : ComputeTable.State) (acc : ℕ) (i : Fin 3) :
    acc < (stampOfAcc st acc).recordExponent i := by
  cases st <;> simp only [stampOfAcc] <;> first | omega | (split_ifs <;> omega)

/-- **Every `stampOfAcc` record slot is inside the row's own line window.**  Unconditional in `i`:
the live slots are `acc+1 … acc+recordCount` by the paper, and the padding slots
(`mem_record = (0,0,0,0)`, the paper) reuse a line the row already consumed rather
than inventing a new one. -/
theorem stampOfAcc_recordExponent_le_row (st : ComputeTable.State) (acc : ℕ) (i : Fin 3) :
    (stampOfAcc st acc).recordExponent i ≤ acc + Nock.Framework.recordCount st := by
  cases st <;>
    simp only [stampOfAcc, Nock.Framework.recordCount] <;>
    first | omega | (split_ifs <;> omega)

/-- The same at the row's own `lnExponent`, which is the paper's `ln`. -/
theorem stampOfAcc_recordExponent_le_lnExponent
    (st : ComputeTable.State) (acc : ℕ) (i : Fin 3) :
    (stampOfAcc st acc).recordExponent i ≤ (stampOfAcc st acc).lnExponent := by
  rw [stampOfAcc_lnExponent]
  exact stampOfAcc_recordExponent_le_row st acc i

/-- `getRecordExp` (`GenMem.lean:1035`) reads slots by *list position*, so it can be asked for a
slot beyond `recordCount`; it still never leaves the row's line window. -/
theorem getRecordExp_stampOfAcc_le_lnExponent
    (st : ComputeTable.State) (acc : ℕ) (j : ℕ) :
    getRecordExp (stampOfAcc st acc) j ≤
      (stampOfAcc st acc).lnExponent := by
  unfold getRecordExp
  split
  · exact stampOfAcc_recordExponent_le_lnExponent st acc _
  · exact Nat.zero_le _

end StampWindow

/-! ## §B. The generated BFS line-number pass: exponents are line numbers in `1 … L`

`bfsAssign` (`BFSAssign.lean:63`) stamps BFS position `i` with `stampOfAcc _ (accAt t (i-1))`, and
`accAt` is the prefix sum of `recordCount` along BFS order — the paper's `ln` column
(the paper, "the number of nodes resolved until now"; the paper, `ln(i) = α·ln(i-1)`).

Two statements here, and the distinction matters:

* `accAt_len_eq_totalRecordCount` — the **identification** of the generator's accumulator with the
  paper's total record count `L` of the committed compute rows.  This is what makes the bound below
  the paper's `L < orderOf α` window rather than a fresh named constant.
* `bfsAssign_extract_recordExp_le_totalRecordCount` — every extracted memory-record exponent is
  `≤ L`, with **no slack**.  `GenSemanticLmIO.bfsAssign_extract_recordExp_le` already had this with
  a `+ 3`; the slack came from bounding a row's slots by `acc + 3` instead of by the row's own
  `ln = acc + recordCount`.  §A removes it. -/

section BfsLineNumbers

variable {K : Type} [Field K]
variable {lmb : K}

/-- The sharp per-row bound: BFS position `i` cannot stamp a record above its own `ln`, which is
`accAt t i`. -/
theorem bfsLabelAt_recordExponent_le_accAt_succ (t : NTree (GenComputeRow K))
    (i : ℕ) (hi : i - 1 < (bfsRows t).length) (j : Fin 3) :
    (bfsLabelAt t i).stamp.recordExponent j ≤ accAt t (i - 1 + 1) := by
  rw [bfsLabelAt_stamp t i hi, accAt_succ_of_lt t (i - 1) hi]
  exact stampOfAcc_recordExponent_le_row _ _ j

/-- `accAt` is monotone, so a row's `ln` is below the whole trace's record count. -/
theorem bfsLabelAt_recordExponent_le_accAt_len (t : NTree (GenComputeRow K))
    (i : ℕ) (hi : i - 1 < (bfsRows t).length) (j : Fin 3) :
    (bfsLabelAt t i).stamp.recordExponent j ≤ accAt t (bfsRows t).length :=
  le_trans (bfsLabelAt_recordExponent_le_accAt_succ t i hi j)
    (accAt_mono t _ _ (by omega))

/-- `accAt` as a prefix sum over BFS-assigned stamps. -/
theorem accAt_eq_sum_range' (t : NTree (GenComputeRow K)) :
    ∀ n, n ≤ (bfsRows t).length →
      accAt t n =
        ((List.range' 1 n).map
          (fun i => Nock.Framework.recordCount (bfsLabelAt t i).stamp.state)).sum := by
  intro n
  induction n with
  | zero => intro _; simp [accAt]
  | succ n ih =>
      intro hn
      have hn' : n < (bfsRows t).length := by omega
      rw [accAt_succ_of_lt t n hn', ih (by omega), List.range'_concat, List.map_append]
      have hstate :
          Nock.Framework.recordCount (bfsLabelAt t (1 + n)).stamp.state =
            Nock.Framework.recordCount (bfsRows t)[n].skel.state := by
        have hi : 1 + n - 1 < (bfsRows t).length := by omega
        rw [bfsLabelAt_stamp t (1 + n) hi, stampOfAcc_state]
        simp only [show 1 + n - 1 = n from by omega]
      simp [hstate]

/-- **The generator's accumulator IS the paper's `L`.**  `accAt t` at the end of the BFS list is
`totalRecordCount` of the committed compute rows — `ForestExponentWindow`'s `L`. -/
theorem accAt_len_eq_totalRecordCount (t : NTree (GenComputeRow K)) :
    accAt t (bfsRows t).length = totalRecordCount (bfsStamps (bfsAssign t)) := by
  rw [accAt_eq_sum_range' t _ le_rfl, bfsStamps_bfsAssign, totalRecordCount, List.map_map,
    bfsRows_length]
  rfl

/-- **Every extracted memory-record exponent is a compute-table line number `≤ L`.**  No slack: the
`+ 3` of `GenSemanticLmIO.bfsAssign_extract_recordExp_le` is gone. -/
theorem bfsAssign_extract_recordExp_le_accAt (t : NTree (GenComputeRow K))
    {n : NTree (GenComputeRow K)} (hn : InTree (bfsAssign t) n)
    {r : MemRecordReq} (hr : r ∈ extractNodeReqs n.label) :
    r.recordExp ≤ accAt t (bfsRows t).length := by
  have hnF : n ∈ bfsForest [bfsAssign t] :=
    (mem_bfsForest _ n).mpr ⟨_, List.mem_singleton.mpr rfl, hn⟩
  have hmem : n.label ∈ (bfsForest [bfsAssign t]).map NTree.label :=
    List.mem_map.mpr ⟨n, hnF, rfl⟩
  rw [bfsAssign_bfsForest_labels] at hmem
  obtain ⟨i, hi, hieq⟩ := List.mem_map.mp hmem
  have hi' := lt_bfsRows_of_mem_range' hi
  obtain ⟨k, hk⟩ := extractNodeReqs_recordExp n.label r hr
  rw [hk]
  refine getRecordExp_le n.label.stamp _ k ?_
  intro j
  rw [← hieq]
  exact bfsLabelAt_recordExponent_le_accAt_len t i hi' j

/-- The same, stated at the paper's `L` -/
theorem bfsAssign_extract_recordExp_le_totalRecordCount (t : NTree (GenComputeRow K))
    {n : NTree (GenComputeRow K)} (hn : InTree (bfsAssign t) n)
    {r : MemRecordReq} (hr : r ∈ extractNodeReqs n.label) :
    r.recordExp ≤ totalRecordCount (bfsStamps (bfsAssign t)) := by
  rw [← accAt_len_eq_totalRecordCount]
  exact bfsAssign_extract_recordExp_le_accAt t hn hr

end BfsLineNumbers

/-! ## §C. Through the served-memory builders, and through threading

`GenSemanticLmIO.genMemForestFromTree_exp_le` already carries the whole induction through
`genAnnotatedNounWalk` / `genAnnotatedVerify` / `genAnnotatedDescent` /
`genAnnotatedDescentCont` / `genAnnotatedChainedInner` / `genAnnotatedChainedTree` /
`genRowMemForest` / `genMemForestFromTree`, generically in the bound `N`.  Nothing is rebuilt
here: §B supplies the sharp `N = L` and this section pushes the result through
`threadGenForest`, which is the last step to the *committed* forest `genMemoryForest`
(`GenSemanticDataParts.lean:43`).

`threadGenForest` rewrites only the LogUp accumulator columns of `row`; the committed Nat
exponents are untouched.  That is `genMemoryStamps_threadGenForest`, the timestamp analogue of
`GenSemanticLmIO.genSemanticSkeleton_threadGenForest`. -/

section ServedForest

variable {K : Type} [Field K]
variable {lmb : K}

/-- **Threading does not move a committed timestamp.**  Same shape as
`genSemanticSkeleton_threadGenForest`, on the Nat exponents instead of the skeleton. -/
theorem genMemoryStamps_threadGenForest (inp : MemoryTable.Inputs K) (acc : K)
    (mf : List (NTree (GenMemoryRow K))) :
    genMemoryStamps (threadGenForest inp acc mf) = genMemoryStamps mf := by
  have hmap : ∀ l : List (NTree (GenMemoryRow K)),
      l.map (fun n => n.label.stamp) = (l.map NTree.label).map GenMemoryRow.stamp := by
    intro l; rw [List.map_map]; rfl
  unfold genMemoryStamps
  rw [hmap, hmap, threadGenForest_bfs_labels, threadGenRows_map_stamp]

/-- **Every committed memory-row exponent of the generated served forest is a compute-table line
number `≤ L`.**  Generated scope: `∀ E z α` and `∀` compute tree, no program and no field
constraint, but the statement is about `genMemForestFromTree` — the generator's own forest. -/
theorem genMemForestFromTree_stamp_exp_le_totalRecordCount
    (E : Noun → ComputeTable.FP K) (z α : K) (t : NTree (GenComputeRow K))
    {st : MemoryTimestampRow}
    (hst : st ∈ genMemoryStamps (genMemForestFromTree E z α lmb (bfsAssign t))) :
    st.recordExponent ≤ totalRecordCount (bfsStamps (bfsAssign t)) := by
  simp only [genMemoryStamps, List.mem_map] at hst
  obtain ⟨v, hv, rfl⟩ := hst
  obtain ⟨root, hroot, hin⟩ := (mem_bfsForest _ v).mp hv
  exact genMemForestFromTree_exp_le E z α _ (bfsAssign t)
    (fun n hn r hr => bfsAssign_extract_recordExp_le_totalRecordCount t hn hr)
    root hroot v hin

/-- The same on the **committed** (threaded) forest a generated configuration publishes. -/
theorem genMemoryForest_stamp_exp_le_totalRecordCount
    (z α : K) (inp : MemoryTable.Inputs K) (t : NTree (GenComputeRow K))
    {st : MemoryTimestampRow}
    (hst : st ∈ genMemoryStamps (genMemoryForest z α lmb inp t)) :
    st.recordExponent ≤ totalRecordCount (bfsStamps (bfsAssign (airReorder t))) := by
  rw [genMemoryForest, genMemoryStamps_threadGenForest] at hst
  exact genMemForestFromTree_stamp_exp_le_totalRecordCount (encC z) z α (airReorder t) hst

end ServedForest

/-! ## §D. Two generic bridges

Both of these are `∀`-generic and **assume** the exponent bound; neither proves it.  They exist so
that §E can hand §B/§C's *proved* bound straight to `GenWorkloadBounds`.

* `committedExponentWindow_of_maxTemplateRecordExponent` is `∀ T : ProductionStrategy F K`.
* `maxTemplateRecordExponent_executionTemplate` and
  `data_committedMemoryExponent_le` are `∀ D : Data E`.

`ForestExponentWindow.wrapDataExponents` shows the *bound itself* is false for a general `D`, so
these lemmas are exactly as strong as their hypotheses and no stronger. -/

section GenericBridges

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {lmb : K}
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

theorem foldr_max_le {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) : l.foldr max 0 ≤ B := by
  induction l with
  | nil => simp
  | cons a tl ih =>
      simp only [List.foldr_cons, max_le_iff]
      exact ⟨h a (by simp), ih fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

/-- **`∀ T : ProductionStrategy F K`.**  A row-level bound on committed memory-timestamp exponents
at every seed gives `GenWorkloadBounds.CommittedExponentWindow`.  Every exponent the α-free axis
structure reads is the committed exponent of an actual BFS row
(`ForestExponentWindow.memoryRow_of_alphaFreeRoot_exp`), so this is a pure repackaging — no new
mathematics and no discharge. -/
theorem committedExponentWindow_of_maxTemplateRecordExponent
    (T : ProductionP8Containment.ProductionStrategy F K) (B : ℕ)
    (hmax : ∀ (z : K) (hz : z ≠ 0),
      maxTemplateRecordExponent
        (ProductionAxisStructureVerifier.committedTemplate T.verifier z hz) ≤ B) :
    CommittedExponentWindow T B := by
  intro z hz i e he
  obtain ⟨row, hrow, hev⟩ :=
    ForestExponentWindow.memoryRow_of_alphaFreeRoot_exp
      (ProductionAxisStructureVerifier.committedTemplate T.verifier z hz) i e he
  subst hev
  have h1 : row.timestamp.recordExponent ≤
      maxTemplateRecordExponent
        (ProductionAxisStructureVerifier.committedTemplate T.verifier z hz) := by
    show row.timestamp.recordExponent ≤
      (((ProductionAxisStructureVerifier.committedTemplate T.verifier z hz).memoryRows).map
        fun r => r.timestamp.recordExponent).foldr max 0
    exact le_foldr_max (List.mem_map_of_mem hrow)
  exact h1.trans (hmax z hz)

variable {E : BuildableNockExecution F K}

/-- **`∀ D : Data E`: the committed memory exponents are seed-free.**  `renderMemoryTemplate` copies
the committed node's Nat stamp verbatim (`HonestCommitment.lean:434`), so the published template's
exponent multiset is the committed node forest's, at every seed.  This is the seed-uniformity that
`CommittedExponentWindow`'s `∀ z` needs. -/
theorem maxTemplateRecordExponent_executionTemplate (D : Data E) (z : K) :
    maxTemplateRecordExponent (D.executionTemplate z) =
      ((bfsForest D.memoryNodes).map (fun n => n.label.stamp.recordExponent)).foldr max 0 := by
  unfold maxTemplateRecordExponent
  congr 1
  show ((bfsForest (D.memoryNodes.map (mapNTree (renderMemoryTemplate z)))).map
      NTree.label).map (fun row => row.timestamp.recordExponent) = _
  rw [bfsForest_mapNTree, List.map_map, List.map_map]
  refine List.map_congr_left ?_
  intro n _
  simp [Function.comp, mapNTree_label, renderMemoryTemplate]

/-- **`∀ D : Data E`**, from a bound on the committed node forest.  Still no discharge: `hbnd` is
the hypothesis. -/
theorem data_maxTemplateRecordExponent_le (D : Data E) (B : ℕ)
    (hbnd : ∀ n ∈ bfsForest D.memoryNodes, n.label.stamp.recordExponent ≤ B) (z : K) :
    maxTemplateRecordExponent (D.executionTemplate z) ≤ B := by
  rw [maxTemplateRecordExponent_executionTemplate]
  refine foldr_max_le ?_
  intro x hx
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
  exact hbnd n hn

/-- The committed template of the honest package's production strategy is the `Data` template **at
every seed**, not only the honest one.  `GenericHonestPackage.packageOf_committedTemplate` states
the honest instance; this is the same `rfl` with `z` free, which is what `∀ z` premises need. -/
theorem packageOf_committedTemplate_all_seeds (D : Data E) (hgt : 11 < ringChar K)
    (I : BuildableChips.Inputs E) (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (z : K) (hz : z ≠ 0) :
    ProductionAxisStructureVerifier.committedTemplate
        (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier z hz =
      D.executionTemplate z :=
  rfl

/-- **`∀ D : Data E`: `CommittedExponentWindow` from one committed-forest bound.**  Composition of
the three lemmas above. -/
theorem packageOf_committedExponentWindow (D : Data E) (hgt : 11 < ringChar K)
    (I : BuildableChips.Inputs E) (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (B : ℕ)
    (hbnd : ∀ n ∈ bfsForest D.memoryNodes, n.label.stamp.recordExponent ≤ B) :
    CommittedExponentWindow (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy B := by
  refine committedExponentWindow_of_maxTemplateRecordExponent _ B ?_
  intro z hz
  rw [packageOf_committedTemplate_all_seeds D hgt I hprl hmore hord hordM hrows hgenF hF z hz]
  exact data_maxTemplateRecordExponent_le D B hbnd z

end GenericBridges

/-! ## §E. The payoff on the generated path

**Generated scope.**  Every theorem in this section carries the hypothesis
`D.memoryNodes = genMemoryNodes z α inp t`, i.e. the commitment's memory node forest *is* the
generator's served forest for the compute tree `t`.  `GenHonestData.genData` satisfies it by
`rfl` (it is that field's definition), and `ForestExponentWindow.wrapDataExponents` fails it, which
is exactly the scope separation §D warns about: the hypothesis is what makes the identification
true, and it is a fact about the generator, not about honest executions in general.

`Λ`, the row counts and `L = totalRecordCount (bfsStamps (bfsAssign (airReorder t)))` are all
trace data.  No named residual is left in the bound. -/

section GeneratedPayoff

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {lmb : K}
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- The generated committed **node** forest inherits §C's bound. -/
theorem genMemoryNodes_stamp_exp_le (z α : K) (inp : MemoryTable.Inputs K)
    (t : NTree (GenComputeRow K)) :
    ∀ n ∈ bfsForest (genMemoryNodes z α lmb inp t),
      n.label.stamp.recordExponent ≤
        totalRecordCount (bfsStamps (bfsAssign (airReorder t))) := by
  intro n hn
  rw [genMemoryNodes, bfsForest_mapNTree, List.mem_map] at hn
  obtain ⟨v, hv, rfl⟩ := hn
  have hmem : v.label.stamp ∈ genMemoryStamps (genMemoryForest z α lmb inp t) :=
    List.mem_map.mpr ⟨v, hv, rfl⟩
  simpa [mapNTree_label] using
    genMemoryForest_stamp_exp_le_totalRecordCount z α inp t hmem

variable {E : BuildableNockExecution F K}

/-- **`CommittedExponentWindow` at `B = L`, discharged on the generated path.**  This is the object
`GenWorkloadBounds` names and does not supply. -/
theorem generated_committedExponentWindow
    (D : Data E) (hgt : 11 < ringChar K) (I : BuildableChips.Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (z α : K) (inp : MemoryTable.Inputs K) (t : NTree (GenComputeRow K))
    (hmem : D.memoryNodes = genMemoryNodes z α lmb inp t) :
    CommittedExponentWindow (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
      (totalRecordCount (bfsStamps (bfsAssign (airReorder t)))) := by
  refine packageOf_committedExponentWindow D hgt I hprl hmore hord hordM hrows hgenF hF _ ?_
  rw [hmem]
  exact genMemoryNodes_stamp_exp_le z α inp t

/-- **The axis majorant, fully trace-quantified.**  `fixedAxisWorkload` is at most the committed
memory-root count times the paper's `L`. -/
theorem generated_fixedAxisWorkload_le
    (D : Data E) (hgt : 11 < ringChar K) (I : BuildableChips.Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (z α : K) (inp : MemoryTable.Inputs K) (t : NTree (GenComputeRow K))
    (hmem : D.memoryNodes = genMemoryNodes z α lmb inp t) :
    ProductionP8Containment.fixedAxisWorkload (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy ≤
      (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton.memoryForest.length *
        totalRecordCount (bfsStamps (bfsAssign (airReorder t))) :=
  fixedAxisWorkload_le _ (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.strategy_bindsAll _
    (generated_committedExponentWindow D hgt I hprl hmore hord hordM hrows hgenF hF z α inp t hmem)

/-- **`workload_le_explicit` with no named residual.**  Every summand on the right is trace data:
skeleton row counts, the committed memory-root count, `Λ`, and `L`. -/
theorem generated_workload_le_explicit
    (D : Data E) (hgt : 11 < ringChar K) (I : BuildableChips.Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (z α : K) (inp : MemoryTable.Inputs K) (t : NTree (GenComputeRow K))
    (hmem : D.memoryNodes = genMemoryNodes z α lmb inp t) (Λ : ℕ) :
    ProductionP8Containment.workload (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy Λ
        (ProductionP8Containment.fixedTopologyWorkload (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy)
        (ProductionP8Containment.fixedAxisWorkload (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy) ≤
      1 + (3 + 19 * (SemanticStrategy.computeSkeletonRows
            (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton).length)
            * (2 * Λ - 1) +
        (24 * (SemanticStrategy.computeSkeletonRows
              (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton).length +
          8 * (SemanticStrategy.memorySkeletonRows
              (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton).length) +
        (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton.memoryForest.length *
          totalRecordCount (bfsStamps (bfsAssign (airReorder t))) +
        ProductionP8Containment.formRUniformWorkload
          (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy +
        ProductionP8Containment.reqPairWorkload
          (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
          Λ +
        SizeWindowCounting.sizeWindowRootBound Λ :=
  workload_le_explicit _ (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.strategy_bindsAll Λ _
    (generated_committedExponentWindow D hgt I hprl hmore hord hordM hrows hgenF hF z α inp t hmem)

end GeneratedPayoff

/-! ## §F. The Goldilocks side condition, with `B` replaced by `L`

`GenWorkloadBounds.goldilocks_exists_coin_outside_failureUnion_of_explicit` had two inputs the tree
could not supply: `CommittedExponentWindow T B` and an inequality mentioning `B`.  On the generated
path §E supplies the first with `B = L`, so what remains is an inequality in **skeleton row counts,
the committed memory-root count, `Λ` and the trace's own record count** — nothing named.

⚠ This section mentions `Nock.Field.K` and therefore depends on the blessed
`Nock.Field.goldilocks_prime` axiom.  Nothing in §A–§E does. -/

section GeneratedGoldilocks

variable {F : Type} [Field F] [Algebra F GK]
variable {lmb : GK}

local instance generatedGoldilocksRingCharP : CharP GK (ringChar GK) := ringChar.charP _

/-- **Generated scope, Goldilocks.**  The soundness numerator is below `p³` as soon as the explicit
inequality in trace data holds; the exponent window is *proved*, not assumed. -/
theorem generated_goldilocks_workload_lt_p_cubed
    [FiniteDimensional F GK] {E : BuildableNockExecution F GK}
    (D : Data E) (hgt : 11 < ringChar GK) (I : BuildableChips.Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar GK ∧ E.cfg.memRows < ringChar GK)
    (hgenF : GeneratedField.ClaimGenerated GK D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (z α : GK) (inp : MemoryTable.Inputs GK) (t : NTree (GenComputeRow GK))
    (hmem : D.memoryNodes = genMemoryNodes z α lmb inp t) (Λ : ℕ)
    (hlt :
      1 + (3 + 19 * (SemanticStrategy.computeSkeletonRows
            (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton).length)
            * (2 * Λ - 1) +
        (24 * (SemanticStrategy.computeSkeletonRows
              (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton).length +
          8 * (SemanticStrategy.memorySkeletonRows
              (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton).length) +
        (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton.memoryForest.length *
          totalRecordCount (bfsStamps (bfsAssign (airReorder t))) +
        ProductionP8Containment.formRUniformWorkload
          (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy +
        ProductionP8Containment.reqPairWorkload
          (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
          Λ +
        SizeWindowCounting.sizeWindowRootBound Λ < Nock.Field.p ^ 3) :
    ProductionP8Containment.workload
        (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy Λ
        (ProductionP8Containment.fixedTopologyWorkload
          (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy)
        (ProductionP8Containment.fixedAxisWorkload
          (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy) < Nock.Field.p ^ 3 :=
  lt_of_le_of_lt
    (generated_workload_le_explicit D hgt I hprl hmore hord hordM hrows hgenF hF z α inp t hmem Λ) hlt

/-- **Existence of a coin outside the five-class failure union, on the generated path.**  This is
`GenWorkloadBounds.goldilocks_exists_coin_outside_failureUnion_of_explicit` with its
`CommittedExponentWindow` premise discharged.  As there, this is existence only: it says nothing
about `Accepts`. -/
theorem generated_goldilocks_exists_coin_outside_failureUnion
    [FiniteDimensional F GK] {E : BuildableNockExecution F GK}
    (D : Data E) (hgt : 11 < ringChar GK) (I : BuildableChips.Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar GK ∧ E.cfg.memRows < ringChar GK)
    (hgenF : GeneratedField.ClaimGenerated GK D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (z α : GK) (inp : MemoryTable.Inputs GK) (t : NTree (GenComputeRow GK))
    (hmem : D.memoryNodes = genMemoryNodes z α lmb inp t) (Λ : ℕ)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus GK
      (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton Λ)
    (lmbU : GK)
    (hwindowBound : SizeWindowCounting.SizeWindowNounsBoundedBy
      (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton Λ)
    (hlt :
      1 + (3 + 19 * (SemanticStrategy.computeSkeletonRows
            (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton).length)
            * (2 * Λ - 1) +
        (24 * (SemanticStrategy.computeSkeletonRows
              (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton).length +
          8 * (SemanticStrategy.memorySkeletonRows
              (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton).length) +
        (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.skeleton.memoryForest.length *
          totalRecordCount (bfsStamps (bfsAssign (airReorder t))) +
        ProductionP8Containment.formRUniformWorkload
          (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy +
        ProductionP8Containment.reqPairWorkload
          (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
          Λ +
        SizeWindowCounting.sizeWindowRootBound Λ < Nock.Field.p ^ 3) :
    ∃ ω : JointCoins GK,
      ω ∉ ProductionP8Containment.FailureUnion
        (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy C lmbU :=
  goldilocks_exists_coin_outside_failureUnion_of_explicit
    (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
    (GenericHonestPackage.packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.strategy_bindsAll Λ
    (totalRecordCount (bfsStamps (bfsAssign (airReorder t)))) C lmbU hwindowBound
    (generated_committedExponentWindow D hgt I hprl hmore hord hordM hrows hgenF hF z α inp t hmem) hlt

end GeneratedGoldilocks

/-! ## §G. Correction: `forestExponentOrder_of_line_numbers`'s `hmemLine` is *unsatisfiable* here

`ForestExponentWindow.forestExponentOrder_of_line_numbers` consumes

    hmemLine : ∀ stamp ∈ S.memoryRows, ∃ c ∈ S.computeRows, ∃ i : Fin 3,
      (i : ℕ) < Nock.Framework.recordCount c.state ∧ stamp.recordExponent = c.recordExponent i

i.e. the identification on **every** committed memory row.  That is stronger than the paper asks
and cannot be supplied by any generator: the paper speaks of the rows that *request* a
memory record, while the served
forest also contains the `decompose` / `halt` nodes of the noun walk, which
request nothing.  The generator stamps those with exponent `0`
(`gMemRow9 (memDecomposeSkel …) 0`, `GenMem.lean:747,808,824`), and `0` is not a line number:
`ForestExponentWindow.recordExponent_pos` says every live compute record exponent is positive
(the paper, `ln(1) = α`).

So the two theorems below are a *negative* result about the bridge, not about the construction:
`hmemLine` fails on any commitment that publishes one noun-walk node, which is every non-trivial
served forest.  §D/§E therefore do **not** route through
`forestExponentOrder_of_line_numbers`; they route through `maxTemplateRecordExponent`, which reads
only the rows the α-free axis structure actually reads. -/

section HmemLineCorrection

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {lmb : K}

/-- A single zero-exponent committed memory row refutes `hmemLine`.  Proved from
`SemanticTimestampSkeleton.computeRecordOffsets` alone: a live compute record exponent is
`lnPrevExponent + i + 1`, hence positive (the paper, `ln(1) = α`). -/
theorem hmemLine_false_of_zero_exponent
    {base : SemanticStrategy.SemanticSkeleton} (S : SemanticTimestampSkeleton F K base)
    {st : MemoryTimestampRow} (hst : st ∈ S.memoryRows) (hzero : st.recordExponent = 0) :
    ¬ (∀ stamp ∈ S.memoryRows, ∃ c ∈ S.computeRows, ∃ i : Fin 3,
        (i : ℕ) < Nock.Framework.recordCount c.state ∧
          stamp.recordExponent = c.recordExponent i) := by
  intro h
  obtain ⟨c, hc, i, hi, hci⟩ := h st hst
  have hoff := S.computeRecordOffsets c hc i hi
  omega

end HmemLineCorrection

section GeneratedZeroExponent

variable {K : Type} [Field K]
variable {lmb : K}

theorem genAnnotatedRecordTree_children (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (ax e : ℕ) :
    (genAnnotatedRecordTree E z α lmb root child ax e).children =
      (genAnnotatedDescent E z lmb root child ax (α ^ e) e root ax).1 := rfl

theorem genAnnotatedVerify_children (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (e : ℕ) :
    (genAnnotatedVerify E z lmb root child ax ts e).1.children =
      [(genAnnotatedNounWalk E z lmb child).1] := rfl

/-- **Every generated axis descent publishes a zero-exponent row.**  Below axis `2` the descent
terminates at the `verify_child` node whose unique child is the noun walk, whose
root is stamped `0`; at axis `2` or above the descent's own first node is a `decompose` row
stamped `0`. -/
theorem genAnnotatedDescent_has_zero_exponent (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ)
    (currentNoun : Noun) (remainingAxis : ℕ) :
    ∃ u ∈ (genAnnotatedDescent E z lmb root child recAxis ts recordExp
        currentNoun remainingAxis).1,
      ∃ v, InTree u v ∧ v.label.stamp.recordExponent = 0 := by
  rcases Nat.lt_or_ge remainingAxis 2 with hax | hax
  · refine ⟨(genAnnotatedVerify E z lmb root child recAxis ts recordExp).1, ?_, ?_⟩
    · rw [genAnnotatedDescent]
      simp [hax]
    · refine ⟨(genAnnotatedNounWalk E z lmb child).1, ?_, ?_⟩
      · exact InTree.sub (by rw [genAnnotatedVerify_children]; simp) (InTree.here _)
      · exact inTree_walk_exp_eq_zero E z child _ (InTree.here _)
  · rw [genAnnotatedDescent]
    simp only [show ¬ (remainingAxis < 2) from by omega, if_false]
    by_cases hbit : axisTopBit remainingAxis
    · simp only [hbit, if_true, List.mem_singleton, exists_eq_left]
      exact ⟨_, InTree.here _, rfl⟩
    · simp only [hbit, Bool.false_eq_true, if_false, List.mem_singleton, exists_eq_left]
      exact ⟨_, InTree.here _, rfl⟩

/-- **…hence so does every generated served record tree.** -/
theorem genAnnotatedRecordTree_has_zero_exponent (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (ax e : ℕ) :
    ∃ v, InTree (genAnnotatedRecordTree E z α lmb root child ax e) v ∧
      v.label.stamp.recordExponent = 0 := by
  obtain ⟨u, hu, v, hv, hzero⟩ :=
    genAnnotatedDescent_has_zero_exponent E z root child ax (α ^ e) e root ax
  refine ⟨v, InTree.sub ?_ hv, hzero⟩
  rw [genAnnotatedRecordTree_children]
  exact hu

end GeneratedZeroExponent

/-! ## §H. The paper's sentence itself, on the generated path

the paper: the committed timestamp "represents the line number of the compute table at which
the memory record was requested".  On the generated path that is an **equality of lists**, not a
bound: `GenSemanticLmIO.genSemanticRequests_exponents` says the committed request exponents are
`1, 2, …, accAt t |bfsRows t|`, and §B identifies that accumulator with the paper's `L`.  So the
committed request-timestamp exponents are *exactly* the compute-table line numbers.

The response (served-memory) side is where the `0`-stamped noun-walk rows live, so the strongest
list-level statement there is the window `≤ L` — which is what the paper asks for. -/

section PaperSentence

variable {K : Type} [Field K]
variable {lmb : K}

/-- **The identification, as an equality of lists.**  The committed request-timestamp exponents of
any generated trace are exactly the compute-table line numbers `1, …, L`, where `L` is
`ForestExponentWindow.totalRecordCount` of the committed compute rows.  Generated scope; `∀`
compute tree and `∀` memory forest -/
theorem genSemanticRequests_exponents_eq_lineNumbers (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    (genSemanticRequests (genSemanticSkeleton (bfsAssign t) mf)
        (bfsStamps (bfsAssign t))).map CanonicalRecordSlot.exponent =
      (List.range (totalRecordCount (bfsStamps (bfsAssign t)))).map (fun i => i + 1) := by
  rw [genSemanticRequests_exponents, accAt_len_eq_totalRecordCount]

/-- Corollary in the shape `ForestExponentWindow` consumes: every committed request exponent is a
line number in `1 … L`. -/
theorem genSemanticRequests_exponent_le_totalRecordCount (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) {slot : CanonicalRecordSlot}
    (h : slot ∈ genSemanticRequests (genSemanticSkeleton (bfsAssign t) mf)
      (bfsStamps (bfsAssign t))) :
    0 < slot.exponent ∧ slot.exponent ≤ totalRecordCount (bfsStamps (bfsAssign t)) := by
  have hmem : slot.exponent ∈
      (genSemanticRequests (genSemanticSkeleton (bfsAssign t) mf)
        (bfsStamps (bfsAssign t))).map CanonicalRecordSlot.exponent :=
    List.mem_map_of_mem h
  rw [genSemanticRequests_exponents_eq_lineNumbers] at hmem
  obtain ⟨i, hi, hval⟩ := List.mem_map.mp hmem
  rw [List.mem_range] at hi
  omega

/-- **The response side, sharp.**  Every committed response-timestamp exponent of the generated
served forest is a compute-table line number `≤ L`.
`GenSemanticLmIO.genSemanticResponses_exponent_le` had the same statement with a `+ 3`. -/
theorem genSemanticResponses_exponent_le_totalRecordCount
    (E : Noun → ComputeTable.FP K) (z α : K) (u : NTree (GenComputeRow K))
    {slot : CanonicalRecordSlot}
    (h : slot ∈ genSemanticResponses
      (genSemanticSkeleton (bfsAssign u) (genMemForestFromTree E z α lmb (bfsAssign u)))
      (genMemoryStamps (genMemForestFromTree E z α lmb (bfsAssign u)))) :
    slot.exponent ≤ totalRecordCount (bfsStamps (bfsAssign u)) := by
  simp only [genSemanticResponses, List.mem_filterMap] at h
  obtain ⟨pair, hpair, hsome⟩ := h
  have hstamp : pair.2 ∈ genMemoryStamps (genMemForestFromTree E z α lmb (bfsAssign u)) :=
    (List.of_mem_zip hpair).2
  by_cases hst : pair.1.state = MemoryTable.MState.read_root
  · rw [dif_pos hst] at hsome
    injection hsome with hslotEq
    subst hslotEq
    exact genMemForestFromTree_stamp_exp_le_totalRecordCount E z α u hstamp
  · rw [dif_neg hst] at hsome
    cases hsome

end PaperSentence

end Nock.NockVMROM.Thm54.TraceGen

/-! ## Scope and axiom receipts

Read them together: §A–§E and
§G–§H are `∀`-quantified over the compute tree, the memory forest, `E`, `z`, `α` and the field; the
*generated* scope is carried by the objects named (`stampOfAcc`, `bfsAssign`, `genMemForestFromTree`,
`genMemoryNodes`), never by a hypothesis pinning a program, a state, an axis or a seed.

The one deliberately non-generic hypothesis is §E's `hmem : D.memoryNodes = genMemoryNodes z α inp t`
— that *is* the generated scope, stated as a hypothesis on purpose so the boundary is visible. -/

#check @Nock.NockVMROM.Thm54.TraceGen.stampOfAcc_recordExponent_le_row
#check @Nock.NockVMROM.Thm54.TraceGen.accAt_len_eq_totalRecordCount
#check @Nock.NockVMROM.Thm54.TraceGen.bfsAssign_extract_recordExp_le_totalRecordCount
#check @Nock.NockVMROM.Thm54.TraceGen.genMemForestFromTree_stamp_exp_le_totalRecordCount
#check @Nock.NockVMROM.Thm54.TraceGen.genMemoryForest_stamp_exp_le_totalRecordCount
#check @Nock.NockVMROM.Thm54.TraceGen.committedExponentWindow_of_maxTemplateRecordExponent
#check @Nock.NockVMROM.Thm54.TraceGen.packageOf_committedExponentWindow
#check @Nock.NockVMROM.Thm54.TraceGen.generated_committedExponentWindow
#check @Nock.NockVMROM.Thm54.TraceGen.generated_workload_le_explicit
#check @Nock.NockVMROM.Thm54.TraceGen.generated_goldilocks_exists_coin_outside_failureUnion
#check @Nock.NockVMROM.Thm54.TraceGen.hmemLine_false_of_zero_exponent
#check @Nock.NockVMROM.Thm54.TraceGen.genSemanticRequests_exponents_eq_lineNumbers

-- [propext, Classical.choice, Quot.sound]
#print axioms Nock.NockVMROM.Thm54.TraceGen.stampOfAcc_lt_recordExponent
#print axioms Nock.NockVMROM.Thm54.TraceGen.stampOfAcc_recordExponent_le_row
#print axioms Nock.NockVMROM.Thm54.TraceGen.stampOfAcc_recordExponent_le_lnExponent
#print axioms Nock.NockVMROM.Thm54.TraceGen.getRecordExp_stampOfAcc_le_lnExponent
#print axioms Nock.NockVMROM.Thm54.TraceGen.bfsLabelAt_recordExponent_le_accAt_succ
#print axioms Nock.NockVMROM.Thm54.TraceGen.bfsLabelAt_recordExponent_le_accAt_len
#print axioms Nock.NockVMROM.Thm54.TraceGen.accAt_eq_sum_range'
#print axioms Nock.NockVMROM.Thm54.TraceGen.accAt_len_eq_totalRecordCount
#print axioms Nock.NockVMROM.Thm54.TraceGen.bfsAssign_extract_recordExp_le_accAt
#print axioms Nock.NockVMROM.Thm54.TraceGen.bfsAssign_extract_recordExp_le_totalRecordCount
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemoryStamps_threadGenForest
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemForestFromTree_stamp_exp_le_totalRecordCount
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemoryForest_stamp_exp_le_totalRecordCount
#print axioms Nock.NockVMROM.Thm54.TraceGen.foldr_max_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.committedExponentWindow_of_maxTemplateRecordExponent
#print axioms Nock.NockVMROM.Thm54.TraceGen.maxTemplateRecordExponent_executionTemplate
#print axioms Nock.NockVMROM.Thm54.TraceGen.data_maxTemplateRecordExponent_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.packageOf_committedTemplate_all_seeds
#print axioms Nock.NockVMROM.Thm54.TraceGen.packageOf_committedExponentWindow
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemoryNodes_stamp_exp_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.generated_committedExponentWindow
#print axioms Nock.NockVMROM.Thm54.TraceGen.generated_fixedAxisWorkload_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.generated_workload_le_explicit
#print axioms Nock.NockVMROM.Thm54.TraceGen.hmemLine_false_of_zero_exponent
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedRecordTree_children
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedVerify_children
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedDescent_has_zero_exponent
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedRecordTree_has_zero_exponent
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSemanticRequests_exponents_eq_lineNumbers
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSemanticRequests_exponent_le_totalRecordCount
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSemanticResponses_exponent_le_totalRecordCount
-- [propext, Classical.choice, Quot.sound, Nock.Field.goldilocks_prime]
#print axioms Nock.NockVMROM.Thm54.TraceGen.generated_goldilocks_workload_lt_p_cubed
#print axioms Nock.NockVMROM.Thm54.TraceGen.generated_goldilocks_exists_coin_outside_failureUnion

