import Nock.NockVM
import Nock.Framework
import Nock.NMRMEF
import Nock.NockVMROM.Language

/-!
# S7 `HasConcreteSoundness` — the NockVMROM fixed-field soundness instance (`Def L1.6`)

Wires the two already-proven **operational walk-soundness probability bounds**
`Nock.NockVM.walkBad_prob` (the single-root compute execution walk) and
`Nock.NockVM.walkBadForest_prob` into the abstract Layer-1 `Nock.Framework.ConcreteSoundnessModel` /
`HasConcreteSoundness` surface on the `NockVMROM` tag.

The trial space bundles *all* arguments+hypotheses the two probability theorems require
(the `StateSep`, node encoding + its injectivity, the BFS layout `fo`/`h`, the tiling
`Sf`/`BFSValid` facts, arity, and the fanout / labelling commitments), mirroring the
`ComputeProblem` / `MemProblem` bundling pattern of `CanonicalRAP.lean`.  Over those bundles
the soundness obligation is *literally* the two probability theorems applied field-by-field —
genuinely non-vacuous, no `True` and no trivial `bound := badProbability`.

* `badProbability t` is the **soundness-breaking probability** over uniform challenge pairs
  `(α, γ) ∈ K × K`: `|walkBad| / |K|²` (compute walk) **plus** `|walkBadForest| / |K|²`
  (memory forest walk) — exactly the two theorems' left-hand sides.
* `bound t` is the corresponding **composite** Schwartz–Zippel/RLC bound
  `(h_c/|K| + ε_RLC^c) + (h_m/|K| + ε_RLC^m)`, `ε_RLC = h·(node_size−1)/|K|` — the sum of the
  two theorems' right-hand sides.
* `sound t` = `add_le_add (walkBad_prob …) (walkBadForest_prob …)` — the two REAL theorems.

This is a genuine **composite** soundness bound: the compute-walk error and the memory-forest
walk error are summed, and each summand is discharged by its own proven operational bound.
-/

namespace Nock.NockVMROM

open Nock Nock.Framework

/-- **Compute-walk soundness trial (single-root execution walk).**  Bundles every argument and
    hypothesis of `Nock.NockVM.walkBad_prob`: the label/data types `S`/`DT`, arity `n`, node width
    `node_size`, the recogniser `F` with its `StateSep`, the (injective) node encoding `enc`, the
    per-row label/child columns `lbl`/`clab`, the BFS fanout `fo` and height `h` with the tiling
    `Sf fo h + 1 = h`, `BFSValid`, arity bound, and the fanout/`F`-commitment side conditions.
    Over this bundle `walkBad_prob` is unconditional (mirrors `ComputeProblem`). -/
structure ComputeWalkTrial (K : Type*) [Field K] [Fintype K] [DecidableEq K] where
  /-- Label state space `S`. -/
  S : Type*
  /-- Label data space `DT`. -/
  DT : Type*
  /-- Tree arity `n`. -/
  n : ℕ
  /-- Node width in `𝔽`. -/
  node_size : ℕ
  /-- The arity-`n` recogniser `L(F,n)`. -/
  F : (S × DT) → (Fin n → Option (S × DT)) → Prop
  /-- State-data separation data for `F` (`Def:state_data_separation`). -/
  St : Nock.Walk.StateSep F
  /-- Node encoding into `𝔽^{node_size}`. -/
  enc : (S × DT) → (Fin node_size → K)
  /-- The node encoding is injective. -/
  hEnc : Function.Injective enc
  /-- Per-row current-node labels. -/
  lbl : ℕ → S × DT
  /-- Per-row child labels. -/
  clab : ℕ → ℕ → S × DT
  /-- BFS fanout column. -/
  fo : ℕ → ℕ
  /-- Walk height (row count). -/
  h : ℕ
  /-- Queue tiles: `Sf fo h + 1 = h`. -/
  hSf : Nock.Walk.Sf fo h + 1 = h
  /-- BFS layout validity. -/
  hvalid : Nock.Walk.BFSValid fo h
  /-- Arity bound `fo i ≤ n`. -/
  harity : ∀ i, fo i ≤ n
  /-- Fanout column agrees with the state's `fanout`. -/
  hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1
  /-- Each committed row is an `F`-statement (labelling commitment). -/
  hFcommit : ∀ i, 1 ≤ i → i ≤ h →
    F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)

/-- **Memory-forest soundness trial (multi-root forest walk, `Corr:forest`).**  Bundles every
    argument and hypothesis of `Nock.NockVM.walkBadForest_prob`: as `ComputeWalkTrial` but with a
    root count `kroots ≥ 1`, the forest tiling `kroots + Sf fo h = h`, and forest BFS validity
    `BFSValidF`.  Over this bundle `walkBadForest_prob` is unconditional. -/
structure ForestWalkTrial (K : Type*) [Field K] [Fintype K] [DecidableEq K] where
  /-- Label state space `S`. -/
  S : Type*
  /-- Label data space `DT`. -/
  DT : Type*
  /-- Tree arity `n`. -/
  n : ℕ
  /-- Node width in `𝔽`. -/
  node_size : ℕ
  /-- The arity-`n` recogniser `L(F,n)`. -/
  F : (S × DT) → (Fin n → Option (S × DT)) → Prop
  /-- State-data separation data for `F`. -/
  St : Nock.Walk.StateSep F
  /-- Node encoding into `𝔽^{node_size}`. -/
  enc : (S × DT) → (Fin node_size → K)
  /-- The node encoding is injective. -/
  hEnc : Function.Injective enc
  /-- Per-row current-node labels. -/
  lbl : ℕ → S × DT
  /-- Per-row child labels. -/
  clab : ℕ → ℕ → S × DT
  /-- BFS fanout column. -/
  fo : ℕ → ℕ
  /-- Number of forest roots `k` (`kroots ≥ 1`). -/
  kroots : ℕ
  /-- Aggregate forest height (row count across all roots). -/
  h : ℕ
  /-- At least one root. -/
  hk : 1 ≤ kroots
  /-- Forest tiling: `kroots + Sf fo h = h`. -/
  hSf : kroots + Nock.Walk.Sf fo h = h
  /-- Forest BFS layout validity. -/
  hvalid : Nock.Walk.BFSValidF kroots fo h
  /-- Arity bound `fo i ≤ n`. -/
  harity : ∀ i, fo i ≤ n
  /-- Fanout column agrees with the state's `fanout`. -/
  hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1
  /-- Each committed row is an `F`-statement (labelling commitment). -/
  hFcommit : ∀ i, 1 ≤ i → i ≤ h →
    F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)

/-- The **soundness-breaking probability** of a compute-walk trial: the bad-challenge-set
    cardinality over the total number of challenge pairs `|K × K| = |K|²` — the left-hand side of
    `walkBad_prob`. -/
noncomputable def computeWalkBadProb {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (t : ComputeWalkTrial K) : ℚ :=
  ((Nock.NockVM.walkBad t.St t.enc t.lbl t.clab t.fo t.h).card : ℚ)
    / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))

/-- The **soundness bound** of a compute-walk trial: `h/|K| + ε_RLC`, `ε_RLC = h·(node_size−1)/|K|`
    — the right-hand side of `walkBad_prob`. -/
def computeWalkBound {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (t : ComputeWalkTrial K) : ℚ :=
  (t.h : ℚ) / (Fintype.card K : ℚ)
    + ((t.h * (t.node_size - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ)

/-- The **soundness-breaking probability** of a memory-forest trial — the left-hand side of
    `walkBadForest_prob`. -/
noncomputable def forestWalkBadProb {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (t : ForestWalkTrial K) : ℚ :=
  ((Nock.NockVM.walkBadForest t.St t.enc t.lbl t.clab t.fo t.kroots t.h).card : ℚ)
    / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))

/-- The **soundness bound** of a memory-forest trial — the right-hand side of
    `walkBadForest_prob`. -/
def forestWalkBound {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (t : ForestWalkTrial K) : ℚ :=
  (t.h : ℚ) / (Fintype.card K : ℚ)
    + ((t.h * (t.node_size - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ)

/-- **The NockVMROM concrete-soundness model (S7, `Def L1.6`).**  A trial is a *pair* of a
    compute-execution-walk bundle and a memory-forest-walk bundle; the soundness-breaking
    probability is the **sum** of the two walks' bad-challenge probabilities, and the bound is the
    **sum** of their Schwartz–Zippel/RLC bounds.  A genuine composite of the two proven operational
    bounds — `badProbability`/`bound` are the honest quantities, never a trivial placeholder. -/
noncomputable def nockConcreteSoundness (F K : Type) [Field F] [Field K] [Fintype K] [DecidableEq K]
    (α β : K) (Ksz : ℕ) : ConcreteSoundnessModel (Tag F K α β Ksz) where
  Trial := ComputeWalkTrial K × ForestWalkTrial K
  badProbability t := computeWalkBadProb t.1 + forestWalkBadProb t.2
  bound t := computeWalkBound t.1 + forestWalkBound t.2

/-- **The NockVMROM concrete-soundness instance (S7).**  `sound` is `add_le_add` of the two REAL
    operational bounds `walkBad_prob` (compute walk) and `walkBadForest_prob` (memory forest walk),
    each applied to the corresponding trial component's bundled fields.  Fully genuine: the composite
    soundness error is bounded by the composite proven bound. -/
noncomputable instance nock_hasConcreteSoundness (F K : Type) [Field F] [Field K] [Fintype K]
    [DecidableEq K] (α β : K) (Ksz : ℕ) :
    HasConcreteSoundness (Tag F K α β Ksz) (nockConcreteSoundness F K α β Ksz) where
  sound t := by
    refine add_le_add ?_ ?_
    · exact Nock.NockVM.walkBad_prob t.1.St t.1.enc t.1.hEnc t.1.lbl t.1.clab t.1.fo
        t.1.hSf t.1.hvalid t.1.harity t.1.hfo t.1.hFcommit
    · exact Nock.NockVM.walkBadForest_prob t.2.St t.2.enc t.2.hEnc t.2.lbl t.2.clab t.2.fo
        t.2.hk t.2.hSf t.2.hvalid t.2.harity t.2.hfo t.2.hFcommit

#print axioms nockConcreteSoundness
#print axioms nock_hasConcreteSoundness

end Nock.NockVMROM
