/-
  Nock/NockVMROM/Thm54/TraceGen/GenNounRecovery.lean

  **X2 — noun recovery from an accepted committed memory walk.**

  `Def:NMR`'s value domain is `(root_fn, child_fn) ∈ 𝕂³ × 𝕂³`: the AIR sees
  fingerprints, so a noun labelling of the committed walk is prover data in the paper too.  What is
  recoverable — and what this module proves — is that on an accepted walk a labelling *exists*, is
  cons-related at every node, and pins `Noun.slot` at every reachable address.

  ## The direction that matters, and why the collision event is NOT in the existence half

  Decoding an *arbitrary* fingerprint is impossible: `ComputeTable.FP K` is `K³`, the image of
  `GlobalCarryRecognizer.enc` is a thin subset, and `NounRealization`'s own counter-regression
  (`badFP_no_noun_preimage`) exhibits a legal-characteristic fingerprint with no noun preimage.
  `FPDecoder.decodeFP` is therefore total only on the gated domain, and the gate
  (`decodable_iff_boundGate`) is `Iff.rfl` with decodability — it assumes the answer.

  Recovery instead runs **bottom-up along the walk**: the terminal `halt` rows carry a scalar leaf
  value, and the only noun-existence input is that this scalar is a bounded `Nat`-cast
  (`MemoryLeafAtomsRealized`).  Internal nodes are then *constructed*, not decoded — the parent noun
  is literally `Noun.cell` of the children's, and `GlobalCarryRecognizer.enc_cons` turns the row's committed `FP.cons` identity into the
  encoding equation.  So the existence half needs only `z ≠ 0`.

  The counted NPR collision event prices the *other* half: identifying the recovered labelling with a noun the
  prover claims publicly.  That is where `hcast` (injectivity of the leaf cast `ℕ → K` on `[0,q)`,
  the small-characteristic caveat in `NPR.NPR_decomp`'s docstring) enters, via
  `GlobalCarryRecognizer.noun_eq_of_enc_eq`.

  ## What carries the axis

  The recovered object is a `GlobalCarryAxis.MemTree`: its `WF` field *is* the per-node cons relation
  `n = Noun.cell (nounOf l) (nounOf r)` together with the locally updatable axis carry
  `2a / 2a+1`.  `GlobalCarryAxis.memtree_noun_eq_slot` then yields
  `Noun.slot (axisOf m) rootNoun = some (nounOf m)` at *every* reachable node — an arbitrary axis,
  not only the relative `2`/`3` of `GlobalCarryRecognizer.formula_cons_sound`.

  ## Re-read note on `Lem:NPR_decomp`'s third identity

  At source the paper prints
  `Φ(n)₃ = Φ(n_L)₃ + X^{2(λ_L−1)} + X^{2λ_L−1}·Φ(n_R)₃`, whereas `NPR.Phi3_cons` proves
  `Φ(n)₃ = X·Φ(n_L)₃ + X^{2λ_L−1} + X^{2λ_L}·Φ(n_R)₃`.  `Nock/NPR.lean` already records that as a
  corrected transcription, and `ComputeTable.FP.cons`'s `dyck` component is the corrected form
  evaluated at `z` (with `z ≠ 0` covering `z^{2λ_L−1} = size²·z⁻¹`).  So the "evaluated images of
  `NPR_decomp`" claim holds against the *Lean* `Phi3_cons`, not against the printed line; this
  module inherits that correction through `GlobalCarryRecognizer.enc_cons` and does not re-open it.

  ## The labelling is a function of the committed trace and `q`, not of the seed

  `recoveredLabelling` (§A′) is a **definition**, not an existence statement: its arguments are the
  committed walk, the leaf window `q` and a starting address, and `z` does not occur in its type.
  The tree shape gives the `MemTree` skeleton and the committed leaf scalars give the leaves, each
  inverted through the `Nat` cast on `[0,q)` (`leafAtomOf`, unique under `hcast` by
  `leafAtomOf_unique`).  So `recoveryOf_memTree_seed_independent` — the same labelling at two
  different nonzero seeds on the same committed data — is `rfl`, and the collision index set
  `recoveryIndexSet q tree P` of §D is fixed *before* any seed is drawn, which is what makes a
  union bound over `z` legitimate (`slot_of_claimed_root_preseed`).

  Everything here is `∀ z q tree` with `K` an arbitrary field; nothing is fixed to a fixture field
  or to a fixture axis.
-/
import Nock.NockVMROM.Thm54.NounRealization
import Nock.NockVMROM.Thm54.TraceGen.GenGlobalCollision

namespace Nock.NockVMROM.Thm54.TraceGen.GenNounRecovery

open Nock Nock.Walk
open Nock.NockVMROM.Thm54

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## §A.  The recovered labelling -/

/-- **A noun labelling of one committed memory walk.**

`memTree` is a `GlobalCarryAxis.MemTree`, so `wf` is simultaneously

* the per-node **cons relation at the noun level** (`n = Noun.cell (nounOf l) (nounOf r)`), and
* the per-node **axis carry**,

and `rootAxis` anchors the carry at the paper's root address `1`.  `encoding` ties
the recovered root noun to the walk's committed root fingerprint, and `nodeEncoding` ties *every*
recovered node to the committed fingerprint of an actual walk node — so this is a labelling of the
trace, not merely some tree with a matching root. -/
structure MemoryNounRecovery (z : K) (q : ℕ)
    (tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)) where
  memTree : GlobalCarryAxis.MemTree
  wf : GlobalCarryAxis.WF memTree
  rootAxis : GlobalCarryAxis.axisOf memTree = 1
  bounded : FieldEmbedding.BoundedBy q (GlobalCarryAxis.nounOf memTree)
  encoding :
    GlobalCarryRecognizer.enc z (GlobalCarryAxis.nounOf memTree) = memoryTreeRootFP tree
  nodeEncoding :
    ∀ m, GlobalCarryAxis.Sub m memTree →
      ∃ node, InTree tree node ∧
        GlobalCarryRecognizer.enc z (GlobalCarryAxis.nounOf m) = memoryTreeRootFP node

/-! ## §A′.  The recovered labelling is a *function* of the committed trace and `q`

`exists_labelling` below is an existence statement, so nothing in its conclusion says what the
labelling is a function of.  This section removes that: `recoveredLabelling` is an ordinary
recursive **definition** whose arguments are the committed walk `tree`, the leaf window `q`, and a
starting address — **the seed `z` does not appear in its type**.  The tree shape supplies the
`MemTree` skeleton (a `.decompose` row becomes a `.node`, a `.halt` row a `.leaf`, and the
pass-through rows `.read_root`/`.verify_child` are transparent), and the only field-valued input is
the committed leaf scalar of each `halt` row, inverted through the `Nat` cast on the window `[0,q)`.

Consequences, both proved below: the labelling is literally the same object at two different seeds
(`recoveryOf_memTree_seed_independent`, by `rfl`), and the collision index set
`recoveryIndexSet q tree P` of §D can be written down before any seed is drawn. -/

/-- The `Nat` preimage of a committed leaf scalar inside the window `[0,q)`.

A function of `q` and the scalar alone.  It is well specified exactly when the scalar *has* such a
preimage (`MemoryLeafAtomsRealized`), and then `hcast`
(`Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q)`) makes the choice unique — `leafAtomOf_unique`. -/
noncomputable def leafAtomOf (q : ℕ) (v : K) : ℕ :=
  open Classical in
  if h : ∃ k : ℕ, k < q ∧ (k : K) = v then h.choose else 0

theorem leafAtomOf_lt {q : ℕ} {v : K} (h : ∃ k : ℕ, k < q ∧ (k : K) = v) :
    leafAtomOf q v < q := by
  rw [leafAtomOf, dif_pos h]
  exact h.choose_spec.1

theorem leafAtomOf_cast {q : ℕ} {v : K} (h : ∃ k : ℕ, k < q ∧ (k : K) = v) :
    ((leafAtomOf q v : ℕ) : K) = v := by
  rw [leafAtomOf, dif_pos h]
  exact h.choose_spec.2

/-- Under the leaf-cast injectivity `hcast`, `leafAtomOf` is *the* preimage: any bounded `Nat`
witness for the same scalar is equal to it.  So the leaf half of the labelling is determined by the
committed data, not merely chosen. -/
theorem leafAtomOf_unique {q : ℕ} (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    {v : K} {k : ℕ} (hk : k < q) (hv : (k : K) = v) :
    leafAtomOf q v = k := by
  have h : ∃ k : ℕ, k < q ∧ (k : K) = v := ⟨k, hk, hv⟩
  exact hcast (Set.mem_Iio.mpr (leafAtomOf_lt h)) (Set.mem_Iio.mpr hk)
    ((leafAtomOf_cast h).trans hv.symm)

/-- **The recovered labelling, as a function.**  Seed-free: its arguments are the committed memory
walk, the leaf window `q`, and the starting address.

The `_ =>.leaf (Noun.atom 0) a` branch is unreachable under `MemoryFingerprintStructure` (whose
constructors fix each row's arity) and is never used by any theorem below; it only makes the
recursion total. -/
-- the paper (the axis carry the skeleton anchors), 2058 (the decompose row)
noncomputable def recoveredLabelling (q : ℕ) :
    NTree (MemoryTable.MState × MemoryTable.DTmem K) → ℕ → GlobalCarryAxis.MemTree
  | .node (.halt, data) [], a =>
      .leaf (Noun.atom (leafAtomOf q data.2.pt.noun.leaf)) a
  | .node (.decompose, _) [left, right], a =>
      .node
        (Noun.cell
          (GlobalCarryAxis.nounOf (recoveredLabelling q left (2 * a)))
          (GlobalCarryAxis.nounOf (recoveredLabelling q right (2 * a + 1))))
        a
        (recoveredLabelling q left (2 * a))
        (recoveredLabelling q right (2 * a + 1))
  | .node (.read_root, _) [child], a => recoveredLabelling q child a
  | .node (.verify_child, _) [child], a => recoveredLabelling q child a
  | _, a => .leaf (Noun.atom 0) a

@[simp] theorem recoveredLabelling_halt (q : ℕ) (data : MemoryTable.DTmem K) (a : ℕ) :
    recoveredLabelling q (.node (.halt, data) []) a
      = .leaf (Noun.atom (leafAtomOf q data.2.pt.noun.leaf)) a := by
  simp [recoveredLabelling]

@[simp] theorem recoveredLabelling_decompose (q : ℕ) (data : MemoryTable.DTmem K)
    (left right : NTree (MemoryTable.MState × MemoryTable.DTmem K)) (a : ℕ) :
    recoveredLabelling q (.node (.decompose, data) [left, right]) a
      = .node
          (Noun.cell
            (GlobalCarryAxis.nounOf (recoveredLabelling q left (2 * a)))
            (GlobalCarryAxis.nounOf (recoveredLabelling q right (2 * a + 1))))
          a
          (recoveredLabelling q left (2 * a))
          (recoveredLabelling q right (2 * a + 1)) := by
  simp [recoveredLabelling]

@[simp] theorem recoveredLabelling_readRoot (q : ℕ) (data : MemoryTable.DTmem K)
    (child : NTree (MemoryTable.MState × MemoryTable.DTmem K)) (a : ℕ) :
    recoveredLabelling q (.node (.read_root, data) [child]) a
      = recoveredLabelling q child a := by
  simp [recoveredLabelling]

@[simp] theorem recoveredLabelling_verifyChild (q : ℕ) (data : MemoryTable.DTmem K)
    (child : NTree (MemoryTable.MState × MemoryTable.DTmem K)) (a : ℕ) :
    recoveredLabelling q (.node (.verify_child, data) [child]) a
      = recoveredLabelling q child a := by
  simp [recoveredLabelling]

/-- The recovered **root** noun of a committed walk, at the paper's root address `1`.  Seed-free, so it is available as an index before any seed is drawn. -/
noncomputable def recoveredRootNoun (q : ℕ)
    (tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)) : Noun :=
  GlobalCarryAxis.nounOf (recoveredLabelling q tree 1)

/-- The collision index set for one committed walk and one publicly claimed root: the two nouns
the event actually has to separate.  Both are functions of committed trace data and `q`, so **no
seed occurs in this expression** — it can be written down before `z` is drawn, which is what makes
the union bound of §D legitimate rather than circular. -/
noncomputable def recoveryIndexSet (q : ℕ)
    (tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)) (P : Noun) : Finset Noun :=
  {P, recoveredRootNoun q tree}

/-- **The labelling's specification.**  Every field of `MemoryNounRecovery` holds *at the defined
labelling* — the existence statements of §B are corollaries of this, obtained by forgetting which
tree was used.

Note which hypotheses do what: `hleaves` is what makes the leaf preimages real (boundedness and the
leaf encoding), `hz` and `hstructure` are what make the encodings match.  None of them enters the
labelling itself. -/
-- the paper, 1292-1295/1301 (axis carry), 1404, 2058
theorem recoveredLabelling_spec {z : K} (hz : z ≠ 0) {q : ℕ}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hstructure : MemoryFingerprintStructure z tree)
    (hleaves : MemoryLeafAtomsRealized q tree) :
    ∀ a : ℕ,
      GlobalCarryAxis.WF (recoveredLabelling q tree a) ∧
      GlobalCarryAxis.axisOf (recoveredLabelling q tree a) = a ∧
      FieldEmbedding.BoundedBy q (GlobalCarryAxis.nounOf (recoveredLabelling q tree a)) ∧
      GlobalCarryRecognizer.enc z (GlobalCarryAxis.nounOf (recoveredLabelling q tree a))
        = memoryTreeRootFP tree ∧
      (∀ m, GlobalCarryAxis.Sub m (recoveredLabelling q tree a) →
        ∃ node, InTree tree node ∧
          GlobalCarryRecognizer.enc z (GlobalCarryAxis.nounOf m) = memoryTreeRootFP node) := by
  induction hstructure with
  | halt data atomShape =>
      intro a
      have hex : ∃ k : ℕ, k < q ∧ (k : K) = data.2.pt.noun.leaf := hleaves
      have henc :
          GlobalCarryRecognizer.enc z (Noun.atom (leafAtomOf q data.2.pt.noun.leaf))
            = data.2.pt.noun := by
        rw [GlobalCarryRecognizer.enc_atom]
        exact ComputeTable.FP.ext atomShape.1.symm atomShape.2.symm (leafAtomOf_cast hex)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show (Noun.atom (leafAtomOf q data.2.pt.noun.leaf)).isAtom = true
        rfl
      · rfl
      · exact leafAtomOf_lt hex
      · exact henc
      · intro m hsub
        rw [recoveredLabelling_halt] at hsub
        cases hsub with
        | refl => exact ⟨_, InTree.here _, henc⟩
  | decompose data left right consEq leftStructure rightStructure ihLeft ihRight =>
      intro a
      obtain ⟨hleavesLeft, hleavesRight⟩ := hleaves
      obtain ⟨hwfL, haxL, hbL, hencL, hnodeL⟩ := ihLeft hleavesLeft (2 * a)
      obtain ⟨hwfR, haxR, hbR, hencR, hnodeR⟩ := ihRight hleavesRight (2 * a + 1)
      have henc :
          GlobalCarryRecognizer.enc z
              (Noun.cell
                (GlobalCarryAxis.nounOf (recoveredLabelling q left (2 * a)))
                (GlobalCarryAxis.nounOf (recoveredLabelling q right (2 * a + 1))))
            = data.2.pt.noun := by
        rw [GlobalCarryRecognizer.enc_cons hz, hencL, hencR]
        exact consEq.symm
      refine ⟨⟨rfl, haxL, haxR, hwfL, hwfR⟩, rfl, ⟨hbL, hbR⟩, henc, ?_⟩
      intro m hsub
      rw [recoveredLabelling_decompose] at hsub
      cases hsub with
      | refl => exact ⟨_, InTree.here _, henc⟩
      | node_l hsubL =>
          obtain ⟨node, hin, hnodeEnc⟩ := hnodeL _ hsubL
          exact ⟨node, InTree.sub (by simp) hin, hnodeEnc⟩
      | node_r hsubR =>
          obtain ⟨node, hin, hnodeEnc⟩ := hnodeR _ hsubR
          exact ⟨node, InTree.sub (by simp) hin, hnodeEnc⟩
  | readRoot data child passEq childStructure ih =>
      intro a
      obtain ⟨hwf, hax, hb, henc, hnode⟩ := ih hleaves a
      rw [recoveredLabelling_readRoot]
      refine ⟨hwf, hax, hb, henc.trans passEq.symm, ?_⟩
      intro m hsub
      obtain ⟨node, hin, hnodeEnc⟩ := hnode m hsub
      exact ⟨node, InTree.sub (by simp) hin, hnodeEnc⟩
  | verifyChild data child passEq childStructure ih =>
      intro a
      obtain ⟨hwf, hax, hb, henc, hnode⟩ := ih hleaves a
      rw [recoveredLabelling_verifyChild]
      refine ⟨hwf, hax, hb, henc.trans passEq.symm, ?_⟩
      intro m hsub
      obtain ⟨node, hin, hnodeEnc⟩ := hnode m hsub
      exact ⟨node, InTree.sub (by simp) hin, hnodeEnc⟩

/-! ## §B.  Existence, off no bad event at all -/

/-- **The recovery induction.**  Verifier-free fingerprint structure plus bounded atom leaves
assemble an axis-carrying noun labelling at *any* starting address `a`.

This is construction from `GlobalCarryRecognizer.enc_atom` and `enc_cons`, not decoding: the only
hypothesis beyond the accepted structure is `z ≠ 0`.  In particular **no collision event and no
`Nat`-cast injectivity are used** — those price uniqueness (§C), not existence. -/
-- the paper, 1292-1295/1301 (axis carry), 1404 (per-node cons), 2058 (the decompose row)
theorem exists_labelling {z : K} (hz : z ≠ 0) {q : ℕ}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hstructure : MemoryFingerprintStructure z tree)
    (hleaves : MemoryLeafAtomsRealized q tree) :
    ∀ a : ℕ, ∃ mt : GlobalCarryAxis.MemTree,
      GlobalCarryAxis.WF mt ∧
      GlobalCarryAxis.axisOf mt = a ∧
      FieldEmbedding.BoundedBy q (GlobalCarryAxis.nounOf mt) ∧
      GlobalCarryRecognizer.enc z (GlobalCarryAxis.nounOf mt) = memoryTreeRootFP tree ∧
      (∀ m, GlobalCarryAxis.Sub m mt →
        ∃ node, InTree tree node ∧
          GlobalCarryRecognizer.enc z (GlobalCarryAxis.nounOf m) = memoryTreeRootFP node) := by
  intro a
  obtain ⟨hwf, hax, hb, henc, hnode⟩ := recoveredLabelling_spec hz hstructure hleaves a
  exact ⟨recoveredLabelling q tree a, hwf, hax, hb, henc, hnode⟩

/-- **The recovery as a term, not merely a `Nonempty`.**  Its `memTree` is the seed-free
`recoveredLabelling`; `hz` and `hstructure` only discharge the proof fields. -/
-- the paper, 1292-1295, 1404, 2058
noncomputable def recoveryOf {z : K} (hz : z ≠ 0) {q : ℕ}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hstructure : MemoryFingerprintStructure z tree)
    (hleaves : MemoryLeafAtomsRealized q tree) :
    MemoryNounRecovery z q tree where
  memTree := recoveredLabelling q tree 1
  wf := (recoveredLabelling_spec hz hstructure hleaves 1).1
  rootAxis := (recoveredLabelling_spec hz hstructure hleaves 1).2.1
  bounded := (recoveredLabelling_spec hz hstructure hleaves 1).2.2.1
  encoding := (recoveredLabelling_spec hz hstructure hleaves 1).2.2.2.1
  nodeEncoding := (recoveredLabelling_spec hz hstructure hleaves 1).2.2.2.2

@[simp] theorem recoveryOf_memTree {z : K} (hz : z ≠ 0) {q : ℕ}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hstructure : MemoryFingerprintStructure z tree)
    (hleaves : MemoryLeafAtomsRealized q tree) :
    (recoveryOf hz hstructure hleaves).memTree = recoveredLabelling q tree 1 := rfl

@[simp] theorem recoveryOf_rootNoun {z : K} (hz : z ≠ 0) {q : ℕ}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hstructure : MemoryFingerprintStructure z tree)
    (hleaves : MemoryLeafAtomsRealized q tree) :
    GlobalCarryAxis.nounOf (recoveryOf hz hstructure hleaves).memTree
      = recoveredRootNoun q tree := rfl

/-- **The labelling does not depend on the seed.**  Two nonzero seeds, each with its own accepted
fingerprint structure on the *same* committed walk, produce the **same** labelling — the same
`MemTree`, hence the same root noun, the same axes and the same per-node nouns.

This is `rfl`: `recoveredLabelling`'s type does not mention `z`, so the recovery's `memTree` cannot
be a function of it.  It is what a union-bound consumer of §D needs and what the existence-only
form of `exists_labelling` could not supply. -/
theorem recoveryOf_memTree_seed_independent {z₁ z₂ : K} (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) {q : ℕ}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hs₁ : MemoryFingerprintStructure z₁ tree) (hs₂ : MemoryFingerprintStructure z₂ tree)
    (hleaves : MemoryLeafAtomsRealized q tree) :
    (recoveryOf hz₁ hs₁ hleaves).memTree = (recoveryOf hz₂ hs₂ hleaves).memTree := rfl

/-- **X2, existence half.**  An accepted committed memory walk with bounded atom leaves has a noun
labelling, anchored at the paper's root axis `1`. -/
-- the paper, 1292-1295, 1404, 2058
theorem nonempty_recovery {z : K} (hz : z ≠ 0) {q : ℕ}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hstructure : MemoryFingerprintStructure z tree)
    (hleaves : MemoryLeafAtomsRealized q tree) :
    Nonempty (MemoryNounRecovery z q tree) :=
  ⟨recoveryOf hz hstructure hleaves⟩

/-- The recovered root noun realizes the walk's root fingerprint — `root_realized` recovered as a
projection, confirming the two routes agree. -/
theorem MemoryNounRecovery.rootFPRealized {z : K} {q : ℕ}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (R : MemoryNounRecovery z q tree) :
    FPRealized z q (memoryTreeRootFP tree) :=
  ⟨GlobalCarryAxis.nounOf R.memTree, R.bounded, R.encoding⟩

/-! ## §C.  The slot relation at every recovered address -/

/-- **The slot relation, at an arbitrary axis.**  Every node of the recovered labelling is the
genuine `Noun.slot` of the recovered root noun at that node's carried axis. -/
theorem MemoryNounRecovery.slot_of_sub {z : K} {q : ℕ}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (R : MemoryNounRecovery z q tree)
    {m : GlobalCarryAxis.MemTree} (hsub : GlobalCarryAxis.Sub m R.memTree) :
    Noun.slot (GlobalCarryAxis.axisOf m) (GlobalCarryAxis.nounOf R.memTree)
      = some (GlobalCarryAxis.nounOf m) :=
  GlobalCarryAxis.memtree_noun_eq_slot R.memTree R.wf R.rootAxis m hsub

/-- Well-formedness is inherited by every reachable subtree. -/
theorem wf_of_sub {m t : GlobalCarryAxis.MemTree}
    (hsub : GlobalCarryAxis.Sub m t) (hwf : GlobalCarryAxis.WF t) :
    GlobalCarryAxis.WF m := by
  induction hsub with
  | refl => exact hwf
  | node_l h ih =>
      simp only [GlobalCarryAxis.WF] at hwf
      exact ih hwf.2.2.2.1
  | node_r h ih =>
      simp only [GlobalCarryAxis.WF] at hwf
      exact ih hwf.2.2.2.2

/-- **The `Service.served` field shape.**  Exactly `Noun.slot axis root = some child`
(`ServedMemoryTrace.Service.served`), read off the recovered labelling.

What a consumer must still supply to instantiate it from a *committed record* rather than from a
recovered node: (i) that the record's committed `mem.axis` is the node's topological address — that
is `AxisDescent.axis_correct`'s content, which is proved unconditionally but on the reconstructed
walk model `AxisBatching.MTree K`, not on `NTree (MState × DTmem K)`, so a model bridge is needed;
and (ii) that the record's `mem.child` fingerprint is the node's `pt.noun` — the `verify_child` row
of `MemoryTable.eqBlk`, turned into a noun equality by the same collision
event as `claimed_root_eq`. -/
theorem MemoryNounRecovery.served_of_node {z : K} {q : ℕ}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (R : MemoryNounRecovery z q tree)
    {m : GlobalCarryAxis.MemTree} (hsub : GlobalCarryAxis.Sub m R.memTree)
    {axis : ℕ} {child : Noun}
    (haxis : GlobalCarryAxis.axisOf m = axis)
    (hchild : GlobalCarryAxis.nounOf m = child) :
    Noun.slot axis (GlobalCarryAxis.nounOf R.memTree) = some child := by
  subst haxis
  subst hchild
  exact R.slot_of_sub hsub

/-- The recovered labelling's per-node **cons relation** at the noun level, together with the
locally updatable axis carry, stated separately from `WF` for consumers that only want it. -/
-- the paper, 1301 (locally updatable), 1404 (per-node cons)
theorem MemoryNounRecovery.cons_of_sub {z : K} {q : ℕ}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (R : MemoryNounRecovery z q tree)
    {n : Noun} {a : ℕ} {l r : GlobalCarryAxis.MemTree}
    (hsub : GlobalCarryAxis.Sub (.node n a l r) R.memTree) :
    n = Noun.cell (GlobalCarryAxis.nounOf l) (GlobalCarryAxis.nounOf r) ∧
      GlobalCarryAxis.axisOf l = 2 * a ∧ GlobalCarryAxis.axisOf r = 2 * a + 1 := by
  have hwf := wf_of_sub hsub R.wf
  simp only [GlobalCarryAxis.WF] at hwf
  exact ⟨hwf.1, hwf.2.1, hwf.2.2.1⟩

/-! ## §D.  Faithfulness to a public claim, priced by the counted event -/

section Uniqueness

variable [Fintype K] [DecidableEq K]

/-- **X2, uniqueness half.**  Off the counted NPR collision event, a publicly claimed root noun
whose encoding is the walk's committed root fingerprint *is* the recovered root noun.

`hcast` is the small-characteristic caveat of `NPR.NPR_decomp`'s docstring: injectivity of the leaf
cast `ℕ → K` on the window `[0,q)`. -/
-- the paper, 1181-1184 (fn), 1188-1194 (lem:ion_univariate_sec)
theorem MemoryNounRecovery.claimed_root_eq {z : K} {q : ℕ}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (R : MemoryNounRecovery z q tree)
    {S : Finset Noun}
    (hgood : z ∉ GenGlobalCollision.globalBadSeeds (K := K) S)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hb : ∀ n ∈ S, FieldEmbedding.BoundedBy q n)
    {P : Noun} (hP : P ∈ S) (hRmem : GlobalCarryAxis.nounOf R.memTree ∈ S)
    (hPenc : GlobalCarryRecognizer.enc z P = memoryTreeRootFP tree) :
    P = GlobalCarryAxis.nounOf R.memTree :=
  GenGlobalCollision.eq_of_enc_eq_of_good hgood hcast hb hP hRmem
    (hPenc.trans R.encoding.symm)

/-- **X2, assembled.**  A recovered labelling, a seed outside the counted collision event, and a
publicly claimed root noun matching the committed root fingerprint give the paper's slot relation
`Noun.slot axis root = some child` at *every* address the walk covers — for the **claimed** root,
not merely for a recovered one. -/
-- the paper, 1322-1325, 1404
theorem MemoryNounRecovery.slot_of_claimed_root {z : K} {q : ℕ}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (R : MemoryNounRecovery z q tree)
    {S : Finset Noun}
    (hgood : z ∉ GenGlobalCollision.globalBadSeeds (K := K) S)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hb : ∀ n ∈ S, FieldEmbedding.BoundedBy q n)
    {P : Noun} (hP : P ∈ S) (hRmem : GlobalCarryAxis.nounOf R.memTree ∈ S)
    (hPenc : GlobalCarryRecognizer.enc z P = memoryTreeRootFP tree) :
    ∀ m, GlobalCarryAxis.Sub m R.memTree →
      Noun.slot (GlobalCarryAxis.axisOf m) P = some (GlobalCarryAxis.nounOf m) := by
  have hPR : P = GlobalCarryAxis.nounOf R.memTree :=
    R.claimed_root_eq hgood hcast hb hP hRmem hPenc
  intro m hsub
  rw [hPR]
  exact R.slot_of_sub hsub

/-! ### The index set is bounded by trace data, and fixed before the seed

The event only ever needs the *pair* {claimed root, recovered root}, so its index set is two nouns
per committed root — not a pre-registered census list.  At `S.card ≤ 2` the paper's `k(k−1)(2Λ−1)`
numerator is `2(2Λ−1)`.

The order of quantifiers is now settled rather than caveated.  `recoveryIndexSet q tree P` is
`{P, recoveredRootNoun q tree}`, and `recoveredRootNoun` is a function of the committed walk and the
window `q` only — no seed occurs in its type, so `recoveryOf_memTree_seed_independent` is `rfl`.
Hence `slot_of_claimed_root_preseed` below can quantify over `z` **inside** a statement whose
index set was already fixed: the bad-seed set is a single finite subset of `K`, bounded by
`recoveryIndexSet_badSeeds_card_le`, and a union bound over it is legitimate.

What is deliberately *not* claimed: that an arbitrary inhabitant of `MemoryNounRecovery z q tree`
has `recoveredLabelling` as its `memTree`.  Off the collision event its *root noun* would coincide
with `recoveredRootNoun` — that is `claimed_root_eq` at the pair `{R`'s root`, the canonical root}` —
but nothing here forces the whole `MemTree`, so the pre-seed statements below are stated about
`recoveredLabelling` itself, which is the object the index set names. -/

/-- The two-noun index set's event bound, from `corr:ion_single_security`. -/
theorem pair_badSeeds_card_le (Λ : ℕ) (P Q : Noun)
    (hP : P.leaves ≤ Λ) (hQ : Q.leaves ≤ Λ) :
    (GenGlobalCollision.globalBadSeeds (K := K) {P, Q}).card ≤ 2 * (2 * Λ - 1) := by
  have hS : ∀ n ∈ ({P, Q} : Finset Noun), n.leaves ≤ Λ := by
    intro n hn
    rcases Finset.mem_insert.mp hn with h | h
    · exact h ▸ hP
    · exact (Finset.mem_singleton.mp h) ▸ hQ
  have hcard : ({P, Q} : Finset Noun).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  have hsub1 : ({P, Q} : Finset Noun).card - 1 ≤ 1 := by omega
  have hmul :
      ({P, Q} : Finset Noun).card * (({P, Q} : Finset Noun).card - 1) ≤ 2 * 1 :=
    Nat.mul_le_mul hcard hsub1
  refine (GenGlobalCollision.globalBadSeeds_card_le (K := K) Λ {P, Q} hS).trans ?_
  refine Nat.mul_le_mul_right _ ?_
  simpa using hmul

/-- **X2, assembled at the two-noun index set.**  The only nouns the event has to separate are the
claimed root and the recovered root, so the whole faithfulness price is `pair_badSeeds_card_le`. -/
theorem MemoryNounRecovery.slot_of_claimed_root_pair {z : K} {q : ℕ}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (R : MemoryNounRecovery z q tree) {P : Noun}
    (hgood : z ∉ GenGlobalCollision.globalBadSeeds (K := K)
      {P, GlobalCarryAxis.nounOf R.memTree})
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbP : FieldEmbedding.BoundedBy q P)
    (hPenc : GlobalCarryRecognizer.enc z P = memoryTreeRootFP tree) :
    ∀ m, GlobalCarryAxis.Sub m R.memTree →
      Noun.slot (GlobalCarryAxis.axisOf m) P = some (GlobalCarryAxis.nounOf m) := by
  refine R.slot_of_claimed_root hgood hcast ?_ ?_ ?_ hPenc
  · intro n hn
    rcases Finset.mem_insert.mp hn with h | h
    · exact h ▸ hbP
    · exact (Finset.mem_singleton.mp h) ▸ R.bounded
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- The pre-seed index set's event bound.  Both leaf-count premises are about committed trace data
and the public claim, so they too are stateable before any seed. -/
theorem recoveryIndexSet_badSeeds_card_le (Λ q : ℕ)
    (tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)) (P : Noun)
    (hP : P.leaves ≤ Λ) (hR : (recoveredRootNoun q tree).leaves ≤ Λ) :
    (GenGlobalCollision.globalBadSeeds (K := K) (recoveryIndexSet q tree P)).card
      ≤ 2 * (2 * Λ - 1) :=
  pair_badSeeds_card_le Λ P (recoveredRootNoun q tree) hP hR

/-- The same bound as a probability over a uniformly sampled seed — the form a union-bound consumer
composes.  Legitimate precisely because `recoveryIndexSet q tree P` does not depend on `z`: the
event is one fixed subset of `K`, and the sampling is over the whole field. -/
-- the paper = 2(2Λ−1)/|K|), 1197-1200 (corr:ion_single_security)
theorem recoveryIndexSet_badSeeds_prob_le (Λ q : ℕ)
    (tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)) (P : Noun)
    (hP : P.leaves ≤ Λ) (hR : (recoveredRootNoun q tree).leaves ≤ Λ) :
    ((GenGlobalCollision.globalBadSeeds (K := K) (recoveryIndexSet q tree P)).card : ℚ)
        / (Fintype.card K)
      ≤ (2 * (2 * Λ - 1) : ℕ) / (Fintype.card K) := by
  have hcard := recoveryIndexSet_badSeeds_card_le (K := K) Λ q tree P hP hR
  have hpos : (0 : ℚ) ≤ (Fintype.card K : ℚ) := by positivity
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hpos

/-- **X2, assembled with the index set chosen before the seed.**

Read the binder order: the committed walk, the window, the public claim, the leaf-cast injectivity
and the leaf realization are all fixed *first*, and `recoveryIndexSet q tree P` is determined by
them; only then is `z` quantified.  So `GenGlobalCollision.globalBadSeeds (recoveryIndexSet q tree P)`
is one fixed finite set — `recoveryIndexSet_badSeeds_card_le` bounds it by `2(2Λ−1)` — and every
seed outside it identifies the claimed root with the canonical labelling's root and hands over the
paper's slot relation at every address the walk covers.

This is the statement the earlier `slot_of_claimed_root_pair` could not make: there the index set
mentioned `R.memTree` for an `R` obtained from `nonempty_recovery` at that same `z`. -/
-- the paper, 1288-1295 (the slot operator and the axis carry), 1322-1325
theorem slot_of_claimed_root_preseed {q : ℕ}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)} {P : Noun}
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbP : FieldEmbedding.BoundedBy q P)
    (hleaves : MemoryLeafAtomsRealized q tree) :
    ∀ z : K, z ≠ 0 →
      z ∉ GenGlobalCollision.globalBadSeeds (K := K) (recoveryIndexSet q tree P) →
      MemoryFingerprintStructure z tree →
      GlobalCarryRecognizer.enc z P = memoryTreeRootFP tree →
      P = recoveredRootNoun q tree ∧
        (∀ m, GlobalCarryAxis.Sub m (recoveredLabelling q tree 1) →
          Noun.slot (GlobalCarryAxis.axisOf m) P = some (GlobalCarryAxis.nounOf m)) := by
  intro z hz hgood hstructure hPenc
  have hb : ∀ n ∈ recoveryIndexSet (K := K) q tree P, FieldEmbedding.BoundedBy q n := by
    intro n hn
    rcases Finset.mem_insert.mp hn with h | h
    · exact h ▸ hbP
    · refine (Finset.mem_singleton.mp h) ▸ ?_
      exact (recoveredLabelling_spec hz hstructure hleaves 1).2.2.1
  have hP : P ∈ recoveryIndexSet (K := K) q tree P := Finset.mem_insert_self _ _
  have hRmem : recoveredRootNoun q tree ∈ recoveryIndexSet (K := K) q tree P :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have heq : P = recoveredRootNoun q tree :=
    GenGlobalCollision.eq_of_enc_eq_of_good hgood hcast hb hP hRmem
      (hPenc.trans (recoveredLabelling_spec hz hstructure hleaves 1).2.2.2.1.symm)
  refine ⟨heq, ?_⟩
  intro m hsub
  rw [heq]
  exact GlobalCarryAxis.memtree_noun_eq_slot _
    (recoveredLabelling_spec hz hstructure hleaves 1).1
    (recoveredLabelling_spec hz hstructure hleaves 1).2.1 m hsub

end Uniqueness

/-! ## §E.  From the accepted exact-execution language

The tree-level premises above are not assumptions on the carrier: production exact `Fmem` topology
already forces `MemoryFingerprintStructure` (`MemoryFingerprintStructure.of_rvtWithArity`), and the
accepted layer supplies the shared seed and `z ≠ 0`.  Only the bounded-atom-leaf input remains, and
it is already a field of `ExactExecutionNounRealization`. -/

/-- The accepted layer's own fingerprint structure at the config seed, extracted so that both the
existence form and the canonical-labelling form below can use it. -/
-- the paper, 2058
theorem fingerprintStructure_of_language {q : ℕ} {cfg : ExactConfig F K}
    {exec : ExactExecution cfg}
    (h : NounRealizedTraversableChainedSemanticExactLanguage q cfg exec)
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (htree : tree ∈ exec.memoryForest) :
    MemoryFingerprintStructure cfg.challenges.z tree := by
  have hload :=
    exactLanguage_challenges_loadBearing
      h.traversable.chained.semantic.toExactLanguage
  have hseed :
      ∀ node, InTree tree node → node.label.2.1.z = cfg.challenges.z := by
    intro node hnode
    have hnodeBfs : node ∈ bfsForest exec.memoryForest :=
      (mem_bfsForest exec.memoryForest node).mpr ⟨tree, htree, hnode⟩
    have hrow : node.label ∈ exec.memoryRows := by
      change node.label ∈ (bfsForest exec.memoryForest).map NTree.label
      exact List.mem_map.mpr ⟨node, hnodeBfs, rfl⟩
    exact (hload.2 node.label hrow).1
  exact MemoryFingerprintStructure.of_rvtWithArity
    cfg.challenges.z tree
    (h.traversable.memory_topology tree htree) hseed

/-- **X2 at the accepted execution.**  Every authoritative committed memory root of an accepted
noun-realized exact execution has a full noun labelling with the cons relation and the axis carry at
every node. -/
-- the paper, 1404
theorem nonempty_recovery_of_language {q : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : NounRealizedTraversableChainedSemanticExactLanguage q cfg exec)
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (htree : tree ∈ exec.memoryForest) :
    Nonempty (MemoryNounRecovery cfg.challenges.z q tree) :=
  nonempty_recovery
    h.traversable.chained.z_ne_zero (fingerprintStructure_of_language h htree)
    (h.nounRealization.memoryLeaves tree htree)

/-- The accepted execution's recovery **as a term**, with `memTree = recoveredLabelling q tree 1`
by `rfl` (`recoveryOf_memTree`). -/
noncomputable def recoveryOfLanguage {q : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : NounRealizedTraversableChainedSemanticExactLanguage q cfg exec)
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (htree : tree ∈ exec.memoryForest) :
    MemoryNounRecovery cfg.challenges.z q tree :=
  recoveryOf h.traversable.chained.z_ne_zero (fingerprintStructure_of_language h htree)
    (h.nounRealization.memoryLeaves tree htree)

/-- **The accepted execution's labelling is the seed-free one.** -/
-- the paper, 1404
theorem labelling_of_language {q : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : NounRealizedTraversableChainedSemanticExactLanguage q cfg exec)
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (htree : tree ∈ exec.memoryForest) :
    GlobalCarryAxis.WF (recoveredLabelling q tree 1) ∧
      GlobalCarryAxis.axisOf (recoveredLabelling q tree 1) = 1 ∧
      FieldEmbedding.BoundedBy q (recoveredRootNoun q tree) ∧
      GlobalCarryRecognizer.enc cfg.challenges.z (recoveredRootNoun q tree)
        = memoryTreeRootFP tree ∧
      (∀ m, GlobalCarryAxis.Sub m (recoveredLabelling q tree 1) →
        Noun.slot (GlobalCarryAxis.axisOf m) (recoveredRootNoun q tree)
          = some (GlobalCarryAxis.nounOf m)) := by
  obtain ⟨hwf, hax, hb, henc, -⟩ :=
    recoveredLabelling_spec h.traversable.chained.z_ne_zero
      (fingerprintStructure_of_language h htree)
      (h.nounRealization.memoryLeaves tree htree) 1
  exact ⟨hwf, hax, hb, henc,
    fun m hsub => GlobalCarryAxis.memtree_noun_eq_slot _ hwf hax m hsub⟩

/-- The slot relation at every recovered address of every authoritative committed memory root of an
accepted execution. -/
theorem slot_of_language {q : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : NounRealizedTraversableChainedSemanticExactLanguage q cfg exec)
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (htree : tree ∈ exec.memoryForest) :
    ∃ mt : GlobalCarryAxis.MemTree,
      GlobalCarryAxis.WF mt ∧ GlobalCarryAxis.axisOf mt = 1 ∧
      FieldEmbedding.BoundedBy q (GlobalCarryAxis.nounOf mt) ∧
      GlobalCarryRecognizer.enc cfg.challenges.z (GlobalCarryAxis.nounOf mt)
        = memoryTreeRootFP tree ∧
      (∀ m, GlobalCarryAxis.Sub m mt →
        Noun.slot (GlobalCarryAxis.axisOf m) (GlobalCarryAxis.nounOf mt)
          = some (GlobalCarryAxis.nounOf m)) := by
  obtain ⟨R⟩ := nonempty_recovery_of_language h htree
  exact ⟨R.memTree, R.wf, R.rootAxis, R.bounded, R.encoding, fun m hsub => R.slot_of_sub hsub⟩

end

end Nock.NockVMROM.Thm54.TraceGen.GenNounRecovery
