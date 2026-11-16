import Nock.Framework.Separation
import Nock.Framework.Traversal
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
Verification layer of the framework: the cost models `CostModel` and the parametric `ParamCostModel`, the traversal classes `TraversalModel` and `IsTraversable`, the two-RAP verification model, completeness and soundness data (fixed-field and asymptotic), and the `VerifiableVMCompilation` bundle that collects all of these clauses as explicit parameters.
-/

namespace Nock.Framework

/-! ## Verification layer — cost (S8), two-RAP (S5), completeness (S6), soundness (S7),
    traversal (S4), and the Theorem-5.4 bundle. -/

/-! ### S8 — cost model -/

/-- **`CostModel`.**  Explicit cost data (columns, constraint count, max
    constraint degree, and degree-4 gate count) for the compute and memory chips.  This is ordinary
    data (a structure), not a class; a proof-class `HasCostModel` pins a VM to a `CostModel`. -/
structure CostModel where
  /-- Compute-chip trace columns. -/
  compCols : ℕ
  /-- Compute-chip constraint count. -/
  compConstraints : ℕ
  /-- Compute-chip maximum constraint degree. -/
  compMaxDegree : ℕ
  /-- Compute-chip degree-4 gate count. -/
  compDeg4 : ℕ
  /-- Memory-chip trace columns. -/
  memCols : ℕ
  /-- Memory-chip constraint count. -/
  memConstraints : ℕ
  /-- Memory-chip maximum constraint degree. -/
  memMaxDegree : ℕ
  /-- Memory-chip degree-4 gate count. -/
  memDeg4 : ℕ
deriving DecidableEq, Repr

/-- **`HasCostModel ι cost` (S8).** -/
class HasCostModel (ι : Type u) [VMSystem ι] (cost : CostModel) : Prop where
  /-- Max compute constraint degree is 4. -/
  compMaxDegree_eq_four : cost.compMaxDegree = 4
  /-- Max memory constraint degree is 4. -/
  memMaxDegree_eq_four : cost.memMaxDegree = 4
  memory_fewer_constraints : cost.memConstraints < cost.compConstraints
  memory_fewer_deg4 : cost.memDeg4 < cost.compDeg4

/-! ### S8 — PARAMETRIC (per extension-order `e`) cost model

    A generic affine-in-`e` refinement of `CostModel`/`HasCostModel`: each column/gate count is an
    `AffineE` (`coeffE·e + const`, the 𝕂-columns/gates that replicate per extension slot plus the
    𝔽-columns/gates that do not), and the model additionally records the deployed `+IO` chips as a
    separate comparison target from the base tables.  The Nock instance + AIR faithfulness live in
    `Nock/NockVMROM/Cost.lean`. -/

/-- Affine-in-`e` count `coeffE * e + const` (𝕂-columns/gates × extension order + 𝔽-columns/gates). -/
structure AffineE where
  /-- Coefficient of the extension order `e` (𝕂-side count, replicated per extension slot). -/
  coeffE : ℕ
  /-- Constant 𝔽-side count (does not replicate with `e`). -/
  const  : ℕ
deriving DecidableEq, Repr

/-- Evaluate an affine-in-`e` count at extension order `e`. -/
def AffineE.eval (q : AffineE) (e : ℕ) : ℕ := q.coeffE * e + q.const

/-- Parametric (per extension-order `e`) cost model: base compute/memory + deployed `+IO` chips. -/
structure ParamCostModel where
  /-- Base compute-chip columns (affine in `e`). -/
  compCols : AffineE
  /-- Base compute-chip degree-4 gates (affine in `e`). -/
  compDeg4 : AffineE
  /-- Base memory-chip columns (affine in `e`). -/
  memCols : AffineE
  /-- Base memory-chip degree-4 gates (affine in `e`). -/
  memDeg4 : AffineE
  /-- Deployed `+IO` compute-chip columns (affine in `e`). -/
  compIOCols : AffineE
  /-- Deployed `+IO` compute-chip degree-4 gates (affine in `e`). -/
  compIODeg4 : AffineE
  /-- Deployed `+IO` memory-chip columns (affine in `e`). -/
  memIOCols : AffineE
  /-- Deployed `+IO` memory-chip degree-4 gates (affine in `e`). -/
  memIODeg4 : AffineE
  /-- Compute-chip maximum constraint degree. -/
  compMaxDeg : ℕ
  /-- Memory-chip maximum constraint degree. -/
  memMaxDeg : ℕ
deriving Repr

/-- **`HasParamCostModel ι pcm` (parametric S8).**  Structural (arithmetic) cost-shape claim,
    parametric in `e`.  NOTE (honest): like `HasCostModel` this constrains only the cost DATA, not
    `ι`'s arithmetization (a `VMSystem` carries no AIR), so a reject-all VM can satisfy it — the AIR
    tie is the separate Nock faithfulness theorem `reifiedNockParamCost_faithful`. -/
class HasParamCostModel (ι : Type u) [VMSystem ι] (pcm : ParamCostModel) : Prop where
  /-- Compute-chip max constraint degree is `≤ 4` (the paper's "degree ≤ 4"). -/
  compMaxDeg_le : pcm.compMaxDeg ≤ 4
  /-- Memory-chip max constraint degree is `≤ 4`. -/
  memMaxDeg_le  : pcm.memMaxDeg ≤ 4
  mem_deg4_lt_comp : ∀ e : ℕ, 1 ≤ e → (pcm.memDeg4.eval e) < (pcm.compDeg4.eval e)

/-! ### S4 — traversal

    The Layer-1 typeclass surface for paper `Def:traversable`.  `TraversalModel` carries the
    *labeling data* (label spaces, arity `n`, root counts `k`, and the algebraically-constrainable
    labeling relations `F_i`/`F*_i`) as a class keyed by the `VMSystem` tag `ι` and memory-encoding
    family `M`.  `IsTraversable` is the property that the compute/memory languages are *recognized*
    by the products of the *exact* arity-`n` recursively-verifiable-tree languages
    `∏_i L_RVT^{F_i,n}` (via `Nock.Walk.RVTWithArity`, i.e. `RVT F ∧ ProperArity n`) — toward the
    paper's `L ≡ L_RVT` of the paper carried as a **sound inclusion** plus a
    **walk-structured `F`-row reconstruction** rather than a free-field `φ` identity.  This is the recognition content behind the `Framework.Traversable` structure's `φ`, but stated
    as an index-explicit data-class + property-class surface tied to the VM's sub-verifiers. -/

/-- **S4 traversal data.**  The compute/memory label spaces, the
    tree arity `n`, the root counts `k_comp`/`k_mem`, and the
    labeling relations `F_i : LT → (Fin n → Option LT) → Prop` recognising `L(F_i,n)` on each side. -/
class TraversalModel (ι : Type u) [VMSystem ι] (M : MEF) where
  /-- Compute-side label space `LT_comp`. -/
  ComputeLabel : Type*
  /-- Memory-side label space `LT_mem`. -/
  MemoryLabel : Type*
  /-- Compute-tree arity `n`. -/
  compArity : ℕ
  /-- Memory-tree arity `n`. -/
  memArity : ℕ
  /-- Number of compute roots `k_comp`. -/
  compRoots : ℕ
  /-- Number of memory roots `k_mem`. -/
  memRoots : ℕ
  /-- The compute labeling relations `F_i`. -/
  Fcomp : Fin compRoots → ComputeLabel → (Fin compArity → Option ComputeLabel) → Prop
  /-- The memory labeling relations `F*_i`. -/
  Fmem : Fin memRoots → MemoryLabel → (Fin memArity → Option MemoryLabel) → Prop

/-- **S4 traversability — GENUINE (non-vacuous) recognition.**

    An earlier
    version of this class ALSO carried self-chosen `ComputeLang`/`MemoryLang : Type` fields with
    traversability isomorphisms `φ_comp`/`φ_mem : ComputeLang ≃ ∏_i L_RVT^{F_i,n}`; those held for
    ANY `VMSystem` (take `ComputeLang :=` the RVT product and `φ := Equiv.refl`), so `φ` added no
    recognition content over the two inclusions below and was a type-level identity untied to the
    VM.  Those four free fields are now REMOVED: the class content is EXACTLY the recognition fields
    below (a sound inclusion + a walk-structured reconstruction — `1-1*`, not a full bijection, F4),
    every field of which references either the VM's ACTUAL sub-verifiers
    (`S.computeAccepts`/`S.memoryAccepts`) or the labeling relations `F_i`/`F*_i`:

    * `recognizes_compute`/`recognizes_memory` — the *sound inclusion* `L_RVT^{F_i,n} ⊆ L_comp`
      (resp. memory): every label the labeling relation `F_i` accepts is accepted by the VM's
      own compute (resp. memory) sub-verifier on its readout row.  This is the substantive
      direction of the paper's `L ≡ L_RVT` (cf. `Framework.Fib.fib_slt_RVT`).
    * `compute_recognized`/`memory_recognized` — a *witnessed inhabitant*: the VM's sub-verifier
      genuinely accepts (the readout of) some `F_i`-recognized leaf.
    * `recognized_complete_compute`/`recognized_complete_memory` — the *reverse inclusion*
      `L_comp ⊆ L_RVT^{F_i,n}` (resp. memory): every walk-structured accepting execution
      reconstructs, via inverse-BFS forest reconstruction, to a forest of `RVTWithArity F_i` trees
      whose aggregate BFS labels are the execution rows.

    Because the sound-inclusion and non-vacuity fields quantify over / reference
    `S.computeAccepts`/`S.memoryAccepts`, the class FAILS for a `VMSystem` whose sub-verifier
    rejects everything (or whose `F_i` recognizes an empty tree language) — so it holds for NO
    arbitrary `VMSystem` and rests on NO free-field `Equiv.refl`.  The completeness half
    `L_comp ⊆ L_RVT` (the inverse-BFS forest reconstruction of the flat accepting rows) is PROVEN
    (`recognized_complete_compute`/`_memory`, discharged for Nock via `Nock.Walk.reconForest`
    + `reconForest_RVT`/`reconForest_properArity`/`reconForest_labels`). -/
class IsTraversable.{u, us, uw, c1, c2, a1, a2, a3, a4, a5, a6}
    (ι : Type u) [VMSystem.{u, us, uw} ι] (M : MEF)
    [tm : TraversalModel.{u, c1, c2, us, uw} ι M]
    [S : UniqueMemoryExecutionSeparable.{u, a1, a2, a3, a4, a5, a6, us, uw} ι M] where
  /-- Readout of a compute tree-label into a program `(statement, witness, IO)` triple of the S1
      separation (the row whose sub-verifier the label's `F_i`-recognition entails). -/
  computeReadout : tm.ComputeLabel → S.ProgStatement × S.ProgWitness × S.ProgIO
  /-- Readout of a memory tree-label into a memory `(statement, witness, IO)` triple. -/
  memoryReadout : tm.MemoryLabel → S.MemStatement × S.MemWitness × S.MemIO
  /-- **Compute recognition — sound inclusion `L_RVT^{F_i,n} ⊆ L_comp`.**  Every
      label `lbl` (with any child vector) that the labeling relation `F_i` accepts is accepted by
      the VM's own compute sub-verifier `S.computeAccepts` on its readout row.  References the VM's
      ACTUAL acceptance, so it is not satisfiable by an arbitrary `VMSystem`. -/
  recognizes_compute : ∀ (i : Fin tm.compRoots) (lbl : tm.ComputeLabel)
      (xout : Fin tm.compArity → Option tm.ComputeLabel), tm.Fcomp i lbl xout →
      S.computeAccepts (computeReadout lbl).1 (computeReadout lbl).2.1 (computeReadout lbl).2.2
  /-- **Memory recognition — sound inclusion `L_RVT^{F*_i,n} ⊆ L_mem`.** -/
  recognizes_memory : ∀ (i : Fin tm.memRoots) (lbl : tm.MemoryLabel)
      (xout : Fin tm.memArity → Option tm.MemoryLabel), tm.Fmem i lbl xout →
      S.memoryAccepts (memoryReadout lbl).1 (memoryReadout lbl).2.1 (memoryReadout lbl).2.2
  /-- **Compute non-vacuity witness.**  The VM's compute sub-verifier genuinely accepts (the
      readout of) some `F_i`-recognized leaf — the recognized compute language is inhabited by a
      VM-accepted element.  Fails when the sub-verifier rejects everything or `F_i` is empty. -/
  compute_recognized : ∃ (i : Fin tm.compRoots) (lbl : tm.ComputeLabel),
      tm.Fcomp i lbl (fun _ => none) ∧
      S.computeAccepts (computeReadout lbl).1 (computeReadout lbl).2.1 (computeReadout lbl).2.2
  /-- **Memory non-vacuity witness.** -/
  memory_recognized : ∃ (i : Fin tm.memRoots) (lbl : tm.MemoryLabel),
      tm.Fmem i lbl (fun _ => none) ∧
      S.memoryAccepts (memoryReadout lbl).1 (memoryReadout lbl).2.1 (memoryReadout lbl).2.2
  /-- **Compute completeness — reverse inclusion `L_comp ⊆ L_RVT^{F_i,n}`, the
      inverse-BFS reconstruction half.**  Every *walk-structured accepting compute execution* — a
      row labeling `lbl : ℕ → ComputeLabel` with a fanout column `fo`, `kroots ≥ 1` roots and height
      `h`, whose aggregate BFS layout tiles (`kroots + Sf fo h = h`) and is queue-valid
      (`BFSValidF`), with bounded arity (`fo ≤ compArity`) and per-row `F_i`-recognition of each
      row against its inverse-BFS child slots — reconstructs to a forest of trees, each in the
      EXACT arity-`n` language `L_RVT^{F_i,n}` (`RVTWithArity (Fcomp i)`), whose aggregate
      breadth-first labels reproduce the execution rows `[lbl 1,…,lbl h]`.  References
      the VM's ACTUAL labeling relation `F_i`, so it is a real obligation (an arbitrary `F_i` need
      not admit such a reconstruction). -/
  recognized_complete_compute :
    ∀ (i : Fin tm.compRoots) (fo : ℕ → ℕ) (lbl : ℕ → tm.ComputeLabel) (kroots h : ℕ),
      1 ≤ kroots → kroots + Nock.Walk.Sf fo h = h → Nock.Walk.BFSValidF kroots fo h →
      (∀ k, fo k ≤ tm.compArity) →
      (∀ k, 1 ≤ k → k ≤ h → tm.Fcomp i (lbl k)
          (fun j : Fin tm.compArity =>
            if (j : ℕ) < fo k then some (lbl (Nock.Walk.firstCF kroots fo k + j)) else none)) →
      ∃ ts : List (Nock.Walk.NTree tm.ComputeLabel),
        (∀ t ∈ ts, Nock.Walk.RVTWithArity (tm.Fcomp i) t) ∧
        (Nock.Walk.bfsForest ts).map Nock.Walk.NTree.label = (List.range' 1 h).map lbl
  /-- **Memory completeness — reverse inclusion `L_mem ⊆ L_RVT^{F*_i,n}`.**  The
      memory analogue of `recognized_complete_compute`: every walk-structured accepting memory
      execution reconstructs to a forest of `RVTWithArity (Fmem i)` trees whose aggregate BFS labels
      are the execution rows. -/
  recognized_complete_memory :
    ∀ (i : Fin tm.memRoots) (fo : ℕ → ℕ) (lbl : ℕ → tm.MemoryLabel) (kroots h : ℕ),
      1 ≤ kroots → kroots + Nock.Walk.Sf fo h = h → Nock.Walk.BFSValidF kroots fo h →
      (∀ k, fo k ≤ tm.memArity) →
      (∀ k, 1 ≤ k → k ≤ h → tm.Fmem i (lbl k)
          (fun j : Fin tm.memArity =>
            if (j : ℕ) < fo k then some (lbl (Nock.Walk.firstCF kroots fo k + j)) else none)) →
      ∃ ts : List (Nock.Walk.NTree tm.MemoryLabel),
        (∀ t ∈ ts, Nock.Walk.RVTWithArity (tm.Fmem i) t) ∧
        (Nock.Walk.bfsForest ts).map Nock.Walk.NTree.label = (List.range' 1 h).map lbl


/-- The exported two-RAP surface: compute/memory trial
    spaces with their soundness-breaking probabilities and (Schwartz–Zippel-style) bounds, plus the
    shared-IO acceptance relation `rapIOAccepts` on an `IOWitness` and the `L_mIO^{M,K}` bound.
    Retained for diagnostic artifacts, but no longer consumed by `VerifiableVMCompilation`. -/
structure TwoRAPVerificationModel (ι : Type u) [VMSystem ι] (M : MEF) (F : Type*) [CommRing F] where
  /-- Compute-RAP trial space. -/
  ComputeTrial : Type*
  /-- Memory-RAP trial space. -/
  MemoryTrial : Type*
  /-- Shared-IO witness space. -/
  IOWitness : Type*
  /-- Compute-RAP soundness-breaking probability. -/
  computeBadProbability : ComputeTrial → ℚ
  /-- Memory-RAP soundness-breaking probability. -/
  memoryBadProbability : MemoryTrial → ℚ
  /-- Compute-RAP soundness bound. -/
  computeBound : ComputeTrial → ℚ
  /-- Memory-RAP soundness bound. -/
  memoryBound : MemoryTrial → ℚ
  /-- Shared-IO acceptance relation (the `L_mIO` consistency between the two RAPs). -/
  rapIOAccepts : IOWitness → Prop
  /-- The `L_mIO^{M,K}` bound. -/
  ioBound : ℕ

/-- Both sub-RAPs are sound (bad-event probability `≤`
    bound) and
    the shared-IO language is genuinely inhabited (`∃ w, rapIOAccepts w`) — a real non-vacuity
    obligation the instance must discharge, not a `True` placeholder.  This class remains a
    negative-control API and is not a field or parameter of the paper-facing bundle. -/
class HasTwoRAPVerification (ι : Type u) [VMSystem ι] (M : MEF) (F : Type*) [CommRing F]
    (model : TwoRAPVerificationModel ι M F) : Prop where
  /-- Compute-RAP soundness. -/
  compute_sound : ∀ t, model.computeBadProbability t ≤ model.computeBound t
  /-- Memory-RAP soundness. -/
  memory_sound : ∀ t, model.memoryBadProbability t ≤ model.memoryBound t
  /-- Non-vacuity of the shared-IO language. -/
  shared_io : ∃ w, model.rapIOAccepts w

/-! ### S6 — perfect completeness (algebraic) -/

/-- The problem/execution space with the concrete `accepted` predicate
    (accepted executions) and the `hasSatisfyingAssignment` predicate (existence of a satisfying RAP
    assignment). -/
structure CompletenessModel (ι : Type u) [VMSystem ι] (M : MEF) (F : Type*) [CommRing F] where
  /-- The problem/execution space. -/
  Problem : Type*
  /-- Accepted executions. -/
  accepted : Problem → Prop
  /-- Existence of a satisfying RAP assignment. -/
  hasSatisfyingAssignment : Problem → Prop

/-- Every accepted execution has a satisfying RAP
    assignment: `∀ p, accepted p → hasSatisfyingAssignment p`.  This is algebraic/RAP completeness
    only.  It remains available to diagnose the former compute-only consumed model, but is not a
    field or parameter of the current Theorem-5.4 bundle. -/
class HasPerfectCompleteness (ι : Type u) [VMSystem ι] (M : MEF) (F : Type*) [CommRing F]
    (m : CompletenessModel ι M F) : Prop where
  /-- Accepted ⇒ has a satisfying assignment. -/
  complete : ∀ p, m.accepted p → m.hasSatisfyingAssignment p

/-! ### S7 — soundness: fixed-field (`Def L1.6`) + asymptotic -/

/-- **S7 fixed-field soundness data (`Def L1.6`).**  A trial space with a soundness-breaking
    probability and a (Schwartz–Zippel-style) bound over the fixed field. -/
structure ConcreteSoundnessModel (ι : Type u) [VMSystem ι] where
  /-- Trial space (compute walk + memory forest walk + shared challenge/collision data). -/
  Trial : Type*
  /-- Soundness-breaking probability. -/
  badProbability : Trial → ℚ
  /-- Soundness bound. -/
  bound : Trial → ℚ

/-- **S7 fixed-field soundness (`Def L1.6`).**  On the fixed field, the soundness-breaking
    probability is at most the bound for every trial. -/
class HasConcreteSoundness (ι : Type u) [VMSystem ι] (model : ConcreteSoundnessModel ι) : Prop where
  /-- Fixed-field soundness bound. -/
  sound : ∀ trial, model.badProbability trial ≤ model.bound trial

/-- **S7 security family.**  A family of fields indexed by the security parameter `n : ℕ` (`𝔽_n`),
    over which the asymptotic soundness claim is stated. -/
structure SecurityFamily where
  /-- The field at security parameter `n`. -/
  FieldAt : ℕ → Type*

/-- **Negligibility.**  `f : ℕ → ℝ` is negligible if for every `c : ℕ`, eventually (along
    `Filter.atTop`) `|f n| ≤ (n+1)^(-c)` — decaying faster than any inverse polynomial. -/
def Negligible (f : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∀ᶠ n in Filter.atTop, |f n| ≤ ((n : ℝ) + 1) ^ (-(c : ℤ))

/-- **S7 asymptotic soundness.**  Over a security family `Fam`, the soundness-error
    function `bad : ℕ → ℝ` is negligible in the security parameter. -/
class HasAsymptoticSoundness (Fam : SecurityFamily) (bad : ℕ → ℝ) : Prop where
  /-- The soundness error is negligible. -/
  negligible : Negligible bad

/-! ### The bundle — `VerifiableVMCompilation` -/

universe u uF us uw a1 a2 a3 a4 a5 a6 b1 b2 c1 c2

/-- **Bundle non-vacuity hygiene.**  The top-level language recognized by `VMSystem ι` has a
    member.  This is not an extra clause of `Def:MES`, which permits an empty
    language; it records that the theorem is being applied to a genuinely inhabited named language.
    Keeping the witness as an explicit parameter makes it load-bearing and noncircular. -/
structure LanguageInhabited (ι : Type u) [VMSystem ι] : Prop where
  /-- A statement accepted by the VM with some witness. -/
  mem : ∃ x : VMSystem.Statement ι, Language ι x

/-- **`VerifiableVMCompilation`.**  The Layer-1 conjunction bundling
    every S1–S8 clause:
      * S1 `UniqueMemoryExecutionSeparable` — a type parameter;
      * S2 an explicit canonical-RAP proposition and proof — type parameters;
      * S3 an explicit opcode/memory one-hot proposition and proof — type parameters;
      * S4 an explicit exact traversability proposition and proof — type parameters;
      * S5 an explicit exact two-RAP proposition and proof — type parameters;
      * S6 an explicit exact combined-completeness proposition and proof — type parameters;
      * S7 an explicit fixed-field soundness proposition and proof — type parameters;
      * S8 an explicit exact-cost proposition and proof — type parameters.
    The S1–S8 claims and `LanguageInhabited` witness are explicit
    parameters, so the theorem's *type* pins which separation, RAPs, one-hot table, traversal,
    exact two-RAP verification claim, combined completeness claim, fixed-field soundness event and
    workload, exact cost certificate, and nonempty language are being certified.

    This class intentionally has no fields: all evidence is already present in its dependent
    parameters. -/
class VerifiableVMCompilation (ι : Type u) [VMSystem.{u, us, uw} ι] (M : MEF) (F : Type uF)
    [CommRing F] (NOP MOP : ℕ)
    (SoundnessClaim : Prop) (soundness : SoundnessClaim)
    (CostClaim : Prop) (costVerified : CostClaim)
    (CompletenessClaim : Prop) (completeness : CompletenessClaim)
    (TwoRAPClaim : Prop) (twoRAPVerified : TwoRAPClaim)
    (uniqueMES : UniqueMemoryExecutionSeparable.{u, a1, a2, a3, a4, a5, a6, us, uw} ι M)
    (CanonicalRAPClaim : Prop) (canonicalRAP : CanonicalRAPClaim)
    (OneHotClaim : Prop) (oneHot : OneHotClaim)
    (TraversalClaim : Prop) (traversable : TraversalClaim)
    (languageInhabited : LanguageInhabited ι) : Prop where

end Nock.Framework
