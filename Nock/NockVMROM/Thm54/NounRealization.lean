import Nock.NockVMROM.Thm54.ExactTraversal
import Nock.NockVMROM.Thm54.NodeEncoding
import Nock.GlobalCarryRecognizer
import Nock.Framework.NockInstances
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Exact noun realization for Theorem 5.4

The field tables store NPR fingerprints, not nouns.  This module adds the missing existence
premise explicitly.  It does not define a decoder and makes no opcode- or evaluator-semantics
claim.

There are three separate layers:

* `FPRealized z q fp` says that one bounded, Nat-valued noun encodes to `fp` at the sampled seed.
* exact public-row/tree predicates classify every noun slot as active or zero padding;
* `MemoryFingerprintStructure.root_realized` recursively assembles a root noun from realized atom
  leaves and verifier-free `cons`/pass-through equations.

The noun is proof data, independent of the field seed.  For seed-indexed field families,
`UniformFPRealized` puts the noun existential outside `∀ z`; fixed exact rows use their actual
input seed, which the cumulative accepted language proves equal to the configured sampled seed.

Existence and uniqueness are intentionally separate.  Existence uses `enc_atom`/`enc_cons`.
Uniqueness additionally needs `SepSeed` and bounded Nat-cast injectivity.
-/

namespace Nock.NockVMROM.Thm54

open scoped Classical
open Nock Nock.Walk

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## Fingerprint existence and seed-independent witnesses -/

/-- A field fingerprint is realized when it is the production global-carry encoding of a
`q`-bounded Nat-valued noun at the stated seed. -/
def FPRealized (z : K) (q : ℕ) (fp : ComputeTable.FP K) : Prop :=
  ∃ n : Noun, FieldEmbedding.BoundedBy q n ∧ GlobalCarryRecognizer.enc z n = fp

/-- Proof-carrying form of `FPRealized`.  The witness is a noun, not field data. -/
structure FPRealizationWitness (z : K) (q : ℕ) (fp : ComputeTable.FP K) where
  noun : Noun
  bounded : FieldEmbedding.BoundedBy q noun
  encoding : GlobalCarryRecognizer.enc z noun = fp

/-- Strong all-seed relation for seed-indexed field families.  The noun existential is outside
`∀ z`, so one seed-independent noun supplies every sampled encoding equation. -/
def UniformFPRealized (q : ℕ) (fp : K → ComputeTable.FP K) : Prop :=
  ∃ n : Noun, FieldEmbedding.BoundedBy q n ∧
    ∀ z : K, GlobalCarryRecognizer.enc z n = fp z

theorem uniformFPRealized_at
    {q : ℕ} {fp : K → ComputeTable.FP K}
    (h : UniformFPRealized q fp) (z : K) :
    FPRealized z q (fp z) := by
  obtain ⟨n, hn, henc⟩ := h
  exact ⟨n, hn, henc z⟩

theorem fpRealized_iff_nonempty_witness
    {z : K} {q : ℕ} {fp : ComputeTable.FP K} :
    FPRealized z q fp ↔ Nonempty (FPRealizationWitness z q fp) := by
  constructor
  · rintro ⟨n, hn, henc⟩
    exact ⟨⟨n, hn, henc⟩⟩
  · rintro ⟨w⟩
    exact ⟨w.noun, w.bounded, w.encoding⟩

/-- At a nonzero seed, a realized noun fingerprint cannot be the padding fingerprint. -/
theorem FPRealized.ne_zero
    {z : K} (hz : z ≠ 0) {q : ℕ} {fp : ComputeTable.FP K}
    (h : FPRealized z q fp) :
    fp ≠ 0 := by
  rintro rfl
  obtain ⟨n, -, henc⟩ := h
  have hsize := congrArg ComputeTable.FP.size henc
  simp only [GlobalCarryRecognizer.enc_size, ComputeTable.FP.zero_size] at hsize
  exact (pow_ne_zero n.leaves hz) hsize

/-! ## Active noun slots versus padding -/

/-- Every fingerprint-valued table position is classified explicitly. -/
inductive FPSlotKind
  | active
  | padding
deriving DecidableEq

/-- Active slots carry a realized nonzero noun fingerprint; padding slots are exactly `0`. -/
def FPSlotRealized (z : K) (q : ℕ) :
    FPSlotKind → ComputeTable.FP K → Prop
  | .active, fp => FPRealized z q fp ∧ fp ≠ 0
  | .padding, fp => fp = 0

/-- A memory record is either an active pair of realized noun fingerprints or the exact all-zero
padding record. -/
def MemRecSlotRealized (z : K) (q : ℕ) :
    FPSlotKind → ComputeTable.MemRec K → Prop
  | .active, r =>
      r ≠ ComputeTable.MemRec.zero ∧
        FPSlotRealized z q .active r.root ∧
        FPSlotRealized z q .active r.child
  | .padding, r => r = ComputeTable.MemRec.zero

/-- Realization reads only `root`/`child`, so it survives the row-level `axis := T` rewrite. -/
theorem MemRecSlotRealized.formRRow {z : K} {q : ℕ} {r : ComputeTable.MemRec K} (lmb : K)
    (h : MemRecSlotRealized z q .active r) :
    MemRecSlotRealized z q .active (NockVM.formRRow r lmb) := by
  refine ⟨?_, h.2.1, h.2.2⟩
  intro hz
  apply h.2.1.2
  have hroot := congrArg ComputeTable.MemRec.root hz
  simpa [NockVM.formRRow, ComputeTable.MemRec.zero] using hroot

/-- A memory child cell is active exactly through its noun field, while a padding child is the
whole production `Cell.zero`, including indicator and count coordinates. -/
def MemoryCellSlotRealized (z : K) (q : ℕ) :
    FPSlotKind → MemoryTable.Cell K → Prop
  | .active, c => FPSlotRealized z q .active c.noun
  | .padding, c => c = MemoryTable.Cell.zero

/-- The exact `sf1/sf2/sf3` public fingerprint triple. -/
def computeSubformulaFPs (pub : ComputeTable.Pub K) :
    Fin 3 → ComputeTable.FP K × ComputeTable.FP K × ComputeTable.FP K :=
  ComputeTable.sfTriple pub

/-- The exact `mr1/mr2/mr3` public memory-record slot. -/
def computeMemRec (pub : ComputeTable.Pub K) : Fin 3 → ComputeTable.MemRec K
  | 0 => pub.mr1
  | 1 => pub.mr2
  | 2 => pub.mr3

/-- State-defined active/padding classification of compute subformula slots. -/
def computeSubformulaKind (st : ComputeTable.State) (i : Fin 3) : FPSlotKind :=
  if (i : ℕ) < ComputeTable.fanoutComp st then .active else .padding

/-- State-defined active/padding classification of compute memory-record slots. -/
def computeMemRecKind (st : ComputeTable.State) (i : Fin 3) : FPSlotKind :=
  if (i : ℕ) < Nock.Framework.recordCount st then .active else .padding

/-- State-defined active/padding classification of memory child cells. -/
def memoryChildKind (st : MemoryTable.MState) (i : Fin 2) : FPSlotKind :=
  if (i : ℕ) < MemoryTable.fanoutMem st then .active else .padding

/-- Exact left/right public child-cell projection. -/
def memoryChildCell (pub : MemoryTable.Pub K) : Fin 2 → MemoryTable.Cell K
  | 0 => pub.lc
  | 1 => pub.rc

/-- Only `read_root` and `verify_child` carry a live memory record. -/
def memoryMemRecKind : MemoryTable.MState → FPSlotKind
  | .decompose | .halt => .padding
  | .read_root | .verify_child => .active

/-! ## Exact public rows and trees -/

/-- Noun-existence data for one exact public compute row.

The primary `(s,f,e)` fingerprints are active.  The first `fanoutComp state` subformula triples
are active and every remaining triple is exactly zero.  Likewise, the first `recordCount state`
memory records are active and the rest are exact `MemRec.zero` padding. -/
structure ComputePublicRowNounRealization
    (q : ℕ) (row : ComputePublicLabel K) : Prop where
  subject :
    FPSlotRealized row.2.1.z q .active row.2.2.s
  formula :
    FPSlotRealized row.2.1.z q .active row.2.2.f
  evaluation :
    FPSlotRealized row.2.1.z q .active row.2.2.e
  subformula :
    ∀ i : Fin 3,
      let sf := computeSubformulaFPs row.2.2 i
      FPSlotRealized row.2.1.z q (computeSubformulaKind row.1 i) sf.1 ∧
        FPSlotRealized row.2.1.z q (computeSubformulaKind row.1 i) sf.2.1 ∧
        FPSlotRealized row.2.1.z q (computeSubformulaKind row.1 i) sf.2.2
  memoryRecord :
    ∀ i : Fin 3,
      MemRecSlotRealized row.2.1.z q
        (computeMemRecKind row.1 i) (computeMemRec row.2.2 i)

/-- Noun-existence data for one exact public memory row.

The parent is active.  Child cells use the exact `fanoutMem` active prefix, with whole-cell zero
padding outside it.  The memory record is active only in the two record-carrying states. -/
structure MemoryPublicRowNounRealization
    (q : ℕ) (row : MemoryTable.MState × MemoryTable.DTmem K) : Prop where
  parent :
    FPSlotRealized row.2.1.z q .active row.2.2.pt.noun
  child :
    ∀ i : Fin 2,
      MemoryCellSlotRealized row.2.1.z q
        (memoryChildKind row.1 i) (memoryChildCell row.2.2 i)
  memoryRecord :
    MemRecSlotRealized row.2.1.z q (memoryMemRecKind row.1) row.2.2.mem

def ComputePublicRowsNounRealization
    (q : ℕ) (rows : List (ComputePublicLabel K)) : Prop :=
  rows.Forall (ComputePublicRowNounRealization q)

def MemoryPublicRowsNounRealization
    (q : ℕ) (rows : List (MemoryTable.MState × MemoryTable.DTmem K)) : Prop :=
  rows.Forall (MemoryPublicRowNounRealization q)

/-- Realization of every exact public compute-tree row in canonical BFS order. -/
def ComputePublicTreeNounRealization
    (q : ℕ) (tree : NTree (ComputePublicLabel K)) : Prop :=
  ComputePublicRowsNounRealization q ((bfsForest [tree]).map NTree.label)

/-- Realization of every exact public memory-forest row in canonical aggregate BFS order. -/
def MemoryPublicForestNounRealization
    (q : ℕ) (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))) : Prop :=
  MemoryPublicRowsNounRealization q ((bfsForest forest).map NTree.label)

/-! ## Recursive memory-tree realization -/

/-- The parent noun fingerprint at a node of the exact memory tree. -/
def memoryTreeRootFP
    (tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)) :
    ComputeTable.FP K :=
  tree.label.2.2.pt.noun

/-- Verifier-free fingerprint structure on an exact public memory tree.

This records only atom shape, binary `cons`, and noun-preserving pass-through equations.  It does
not contain `Vmem`, a decoder, an opcode evaluation relation, or a Nock evaluator claim. -/
inductive MemoryFingerprintStructure (z : K) :
    NTree (MemoryTable.MState × MemoryTable.DTmem K) → Prop
  | halt (data : MemoryTable.DTmem K)
      (atomShape : data.2.pt.noun.size = z ∧ data.2.pt.noun.dyck = 0) :
      MemoryFingerprintStructure z (.node (.halt, data) [])
  | decompose (data : MemoryTable.DTmem K)
      (left right : NTree (MemoryTable.MState × MemoryTable.DTmem K))
      (consEq :
        data.2.pt.noun =
          ComputeTable.FP.cons z (memoryTreeRootFP left) (memoryTreeRootFP right))
      (leftStructure : MemoryFingerprintStructure z left)
      (rightStructure : MemoryFingerprintStructure z right) :
      MemoryFingerprintStructure z (.node (.decompose, data) [left, right])
  | readRoot (data : MemoryTable.DTmem K)
      (child : NTree (MemoryTable.MState × MemoryTable.DTmem K))
      (passEq : data.2.pt.noun = memoryTreeRootFP child)
      (childStructure : MemoryFingerprintStructure z child) :
      MemoryFingerprintStructure z (.node (.read_root, data) [child])
  | verifyChild (data : MemoryTable.DTmem K)
      (child : NTree (MemoryTable.MState × MemoryTable.DTmem K))
      (passEq : data.2.pt.noun = memoryTreeRootFP child)
      (childStructure : MemoryFingerprintStructure z child) :
      MemoryFingerprintStructure z (.node (.verify_child, data) [child])

/-- The only noun-existence input to recursive wiring: every terminal fingerprint leaf is the
Nat-cast of a bounded atom. -/
def MemoryLeafAtomsRealized (q : ℕ) :
    NTree (MemoryTable.MState × MemoryTable.DTmem K) → Prop
  | .node (.halt, data) [] =>
      ∃ k : ℕ, k < q ∧ (k : K) = data.2.pt.noun.leaf
  | .node (.decompose, _) [left, right] =>
      MemoryLeafAtomsRealized q left ∧ MemoryLeafAtomsRealized q right
  | .node (.read_root, _) [child] =>
      MemoryLeafAtomsRealized q child
  | .node (.verify_child, _) [child] =>
      MemoryLeafAtomsRealized q child
  | _ => False

/-- Production exact `Fmem` topology already forces the verifier-free fingerprint structure once
all rows are identified with one shared seed.  This theorem extracts that existing structure; it
does not add it as a noun-existence premise. -/
theorem MemoryFingerprintStructure.of_rvtWithArity
    (z : K)
    (tree : NTree (MemoryTable.MState × MemoryTable.DTmem K))
    (htopology : RVTWithArity (MemoryTable.Fmem (K := K)) tree)
    (hseed :
      ∀ node, InTree tree node → node.label.2.1.z = z) :
    MemoryFingerprintStructure z tree := by
  suffices H :
      ∀ n : ℕ,
        ∀ tree : NTree (MemoryTable.MState × MemoryTable.DTmem K),
          sizeOf tree ≤ n →
          RVTWithArity (MemoryTable.Fmem (K := K)) tree →
          (∀ node, InTree tree node → node.label.2.1.z = z) →
          MemoryFingerprintStructure z tree by
    exact H (sizeOf tree) tree le_rfl htopology hseed
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro tree hsize htopology hseed
      have hFcon :=
        (RVT_iff_forall_InTree (MemoryTable.Fmem (K := K)) tree).mp
          htopology.rvt tree (InTree.here tree)
      have hshape :=
        fanout_eq_children_length_of_properArity
          (MemoryTable.mem_stateSep (K := K))
          htopology.rvt htopology.arity tree (InTree.here tree)
      have hrootSeed := hseed tree (InTree.here tree)
      cases tree with
      | node lbl children =>
          obtain ⟨state, data⟩ := lbl
          simp only [NTree.label_node, NTree.children_node] at hFcon hshape hrootSeed hsize
          have hstate : data.2.st = state := hFcon.1.1
          have heq : MemoryTable.eqBlk data.1 data.2 := hFcon.1.2.1.2.1
          have hlink :
              MemoryTable.childLinkMem (state, data)
                (fun i : Fin 2 => (NTree.node (state, data) children).childLabel i) :=
            hFcon.1.2.2.2
          cases state with
          | halt =>
              have hlen : children.length = 0 := by
                change 0 = children.length at hshape
                exact hshape.symm
              have hnil : children = [] := List.eq_nil_of_length_eq_zero hlen
              subst children
              simp only [MemoryTable.eqBlk, hstate] at heq
              exact .halt data ⟨heq.1.trans hrootSeed, heq.2.1⟩
          | decompose =>
              have hlen : children.length = 2 := by
                change 2 = children.length at hshape
                exact hshape.symm
              obtain ⟨left, right, rfl⟩ := List.length_eq_two.mp hlen
              have hleftLink := hlink 0 (by simp [MemoryTable.fanoutMem])
              have hrightLink := hlink 1 (by simp [MemoryTable.fanoutMem])
              simp only [NTree.childLabel, NTree.childOpt, NTree.children_node,
                Fin.val_zero, Fin.val_one, List.getElem?_cons_zero,
                List.getElem?_cons_succ, Option.map_some, MemoryTable.memCell,
                Option.some.injEq] at hleftLink hrightLink
              simp only [MemoryTable.eqBlk, hstate] at heq
              have hleftIn :
                  InTree (NTree.node (MemoryTable.MState.decompose, data) [left, right])
                    left :=
                InTree.sub (by simp) (InTree.here left)
              have hrightIn :
                  InTree (NTree.node (MemoryTable.MState.decompose, data) [left, right])
                    right :=
                InTree.sub (by simp) (InTree.here right)
              have hleftSize :
                  sizeOf left <
                    sizeOf (NTree.node (MemoryTable.MState.decompose, data) [left, right]) := by
                simp only [NTree.node.sizeOf_spec, List.cons.sizeOf_spec,
                  List.nil.sizeOf_spec]
                omega
              have hrightSize :
                  sizeOf right <
                    sizeOf (NTree.node (MemoryTable.MState.decompose, data) [left, right]) := by
                simp only [NTree.node.sizeOf_spec, List.cons.sizeOf_spec,
                  List.nil.sizeOf_spec]
                omega
              have hleftTopology :
                  RVTWithArity (MemoryTable.Fmem (K := K)) left :=
                ⟨RVT_of_InTree htopology.rvt hleftIn,
                  htopology.arity.ofChild (by simp)⟩
              have hrightTopology :
                  RVTWithArity (MemoryTable.Fmem (K := K)) right :=
                ⟨RVT_of_InTree htopology.rvt hrightIn,
                  htopology.arity.ofChild (by simp)⟩
              have hleftStructure :=
                ih (sizeOf left) (by omega) left le_rfl hleftTopology
                  (fun node hnode => hseed node (InTree_trans hleftIn hnode))
              have hrightStructure :=
                ih (sizeOf right) (by omega) right le_rfl hrightTopology
                  (fun node hnode => hseed node (InTree_trans hrightIn hnode))
              apply MemoryFingerprintStructure.decompose data left right
              · calc
                  data.2.pt.noun =
                      ComputeTable.FP.cons z data.2.lc.noun data.2.rc.noun := by
                    simpa [hrootSeed] using heq.1
                  _ = ComputeTable.FP.cons z
                        (memoryTreeRootFP left) (memoryTreeRootFP right) := by
                    rw [← congrArg MemoryTable.Cell.noun hleftLink,
                      ← congrArg MemoryTable.Cell.noun hrightLink]
                    rfl
              · exact hleftStructure
              · exact hrightStructure
          | read_root =>
              have hlen : children.length = 1 := by
                change 1 = children.length at hshape
                exact hshape.symm
              obtain ⟨child, rfl⟩ := List.length_eq_one_iff.mp hlen
              have hchildLink := hlink 0 (by simp [MemoryTable.fanoutMem])
              simp only [NTree.childLabel, NTree.childOpt, NTree.children_node,
                Fin.val_zero, List.getElem?_cons_zero, Option.map_some,
                MemoryTable.memCell, Option.some.injEq] at hchildLink
              simp only [MemoryTable.eqBlk, hstate] at heq
              have hchildIn :
                  InTree (NTree.node (MemoryTable.MState.read_root, data) [child]) child :=
                InTree.sub (by simp) (InTree.here child)
              have hchildSize :
                  sizeOf child <
                    sizeOf (NTree.node (MemoryTable.MState.read_root, data) [child]) := by
                simp only [NTree.node.sizeOf_spec, List.cons.sizeOf_spec,
                  List.nil.sizeOf_spec]
                omega
              have hchildTopology :
                  RVTWithArity (MemoryTable.Fmem (K := K)) child :=
                ⟨RVT_of_InTree htopology.rvt hchildIn,
                  htopology.arity.ofChild (by simp)⟩
              have hchildStructure :=
                ih (sizeOf child) (by omega) child le_rfl hchildTopology
                  (fun node hnode => hseed node (InTree_trans hchildIn hnode))
              apply MemoryFingerprintStructure.readRoot data child
              · exact heq.1.trans
                  (congrArg MemoryTable.Cell.noun hchildLink).symm
              · exact hchildStructure
          | verify_child =>
              have hlen : children.length = 1 := by
                change 1 = children.length at hshape
                exact hshape.symm
              obtain ⟨child, rfl⟩ := List.length_eq_one_iff.mp hlen
              have hchildLink := hlink 0 (by simp [MemoryTable.fanoutMem])
              simp only [NTree.childLabel, NTree.childOpt, NTree.children_node,
                Fin.val_zero, List.getElem?_cons_zero, Option.map_some,
                MemoryTable.memCell, Option.some.injEq] at hchildLink
              simp only [MemoryTable.eqBlk, hstate] at heq
              have hchildIn :
                  InTree (NTree.node (MemoryTable.MState.verify_child, data) [child]) child :=
                InTree.sub (by simp) (InTree.here child)
              have hchildSize :
                  sizeOf child <
                    sizeOf (NTree.node (MemoryTable.MState.verify_child, data) [child]) := by
                simp only [NTree.node.sizeOf_spec, List.cons.sizeOf_spec,
                  List.nil.sizeOf_spec]
                omega
              have hchildTopology :
                  RVTWithArity (MemoryTable.Fmem (K := K)) child :=
                ⟨RVT_of_InTree htopology.rvt hchildIn,
                  htopology.arity.ofChild (by simp)⟩
              have hchildStructure :=
                ih (sizeOf child) (by omega) child le_rfl hchildTopology
                  (fun node hnode => hseed node (InTree_trans hchildIn hnode))
              apply MemoryFingerprintStructure.verifyChild data child
              · exact heq.1.trans
                  (congrArg MemoryTable.Cell.noun hchildLink).symm
              · exact hchildStructure

/-- Recursive existence: bounded atom leaves plus verifier-free structural equations assemble a
bounded root noun.  This is construction from `enc_atom` and `enc_cons`, not decoding an arbitrary
fingerprint. -/
theorem MemoryFingerprintStructure.root_realized
    {z : K} (hz : z ≠ 0) {q : ℕ}
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hstructure : MemoryFingerprintStructure z tree)
    (hleaves : MemoryLeafAtomsRealized q tree) :
    FPRealized z q (memoryTreeRootFP tree) := by
  induction hstructure with
  | halt data atomShape =>
      obtain ⟨k, hk, hleaf⟩ := hleaves
      refine ⟨.atom k, hk, ?_⟩
      rw [GlobalCarryRecognizer.enc_atom]
      exact ComputeTable.FP.ext atomShape.1.symm atomShape.2.symm hleaf
  | decompose data left right consEq leftStructure rightStructure ihLeft ihRight =>
      obtain ⟨hleavesLeft, hleavesRight⟩ := hleaves
      obtain ⟨leftNoun, hleftBounded, hleftEnc⟩ := ihLeft hleavesLeft
      obtain ⟨rightNoun, hrightBounded, hrightEnc⟩ := ihRight hleavesRight
      refine ⟨.cell leftNoun rightNoun, ⟨hleftBounded, hrightBounded⟩, ?_⟩
      rw [GlobalCarryRecognizer.enc_cons hz, hleftEnc, hrightEnc]
      exact consEq.symm
  | readRoot data child passEq childStructure ih =>
      obtain ⟨noun, hbounded, henc⟩ := ih hleaves
      exact ⟨noun, hbounded, henc.trans passEq.symm⟩
  | verifyChild data child passEq childStructure ih =>
      obtain ⟨noun, hbounded, henc⟩ := ih hleaves
      exact ⟨noun, hbounded, henc.trans passEq.symm⟩

/-! ## Uniqueness, separately from existence -/

/-- Two supplied realization witnesses have the same noun only after adding the NPR separating
event and bounded Nat-cast injectivity. -/
theorem FPRealizationWitness.noun_unique
    {z : K} {q : ℕ} {fp : ComputeTable.FP K}
    (left right : FPRealizationWitness z q fp)
    (hsep : GlobalCarryRecognizer.SepSeed z left.noun right.noun)
    (hinj : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q)) :
    left.noun = right.noun :=
  GlobalCarryRecognizer.noun_eq_of_enc_eq z left.noun right.noun
    hsep hinj left.bounded right.bounded (left.encoding.trans right.encoding.symm)

/-- Proof-carrying realizations themselves are unique under the same two hypotheses. -/
theorem FPRealizationWitness.unique
    {z : K} {q : ℕ} {fp : ComputeTable.FP K}
    (left right : FPRealizationWitness z q fp)
    (hsep : GlobalCarryRecognizer.SepSeed z left.noun right.noun)
    (hinj : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q)) :
    left = right := by
  cases left with
  | mk leftNoun leftBounded leftEncoding =>
      cases right with
      | mk rightNoun rightBounded rightEncoding =>
          have hn :
              leftNoun = rightNoun :=
            GlobalCarryRecognizer.noun_eq_of_enc_eq z leftNoun rightNoun
              hsep hinj leftBounded rightBounded
                (leftEncoding.trans rightEncoding.symm)
          subst rightNoun
          rfl

/-! ## Cumulative exact language -/

/-- Realization witnesses on the exact authoritative public compute tree and memory forest.
Only atom-leaf existence is added for recursive memory wiring: production exact topology supplies
the structural `cons`/pass-through equations through `of_rvtWithArity`. -/
structure ExactExecutionNounRealization
    (q : ℕ) (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Prop where
  computeTree :
    ComputePublicTreeNounRealization q exec.computePublicTree
  memoryForest :
    MemoryPublicForestNounRealization q exec.memoryForest
  memoryLeaves :
    ∀ tree ∈ exec.memoryForest,
      MemoryLeafAtomsRealized q tree

/-- It strengthens, and does not redefine, any weaker layer. -/
structure NounRealizedTraversableChainedSemanticExactLanguage
    (q : ℕ) (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Prop where
  traversable : TraversableChainedSemanticExactLanguage cfg exec
  nounRealization : ExactExecutionNounRealization q cfg exec

/-- Proof-carrying members of the cumulative noun-realized exact language. -/
abbrev NounRealizedTraversableChainedAcceptedExecution
    (q : ℕ) (cfg : ExactConfig F K) :=
  { exec : ExactExecution cfg //
    NounRealizedTraversableChainedSemanticExactLanguage q cfg exec }

theorem NounRealizedTraversableChainedSemanticExactLanguage.toTraversable
    {q : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : NounRealizedTraversableChainedSemanticExactLanguage q cfg exec) :
    TraversableChainedSemanticExactLanguage cfg exec :=
  h.traversable

theorem NounRealizedTraversableChainedSemanticExactLanguage.toChained
    {q : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : NounRealizedTraversableChainedSemanticExactLanguage q cfg exec) :
    ChainedSemanticExactLanguage cfg exec :=
  h.traversable.chained

/-- The fixed row equations in the realization predicates use the rows' actual sampled `z`; the
unchanged accepted layer proves those seeds are exactly the configured shared seed. -/
theorem NounRealizedTraversableChainedSemanticExactLanguage.configured_seed_used
    {q : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : NounRealizedTraversableChainedSemanticExactLanguage q cfg exec) :
    (∀ row ∈ exec.computeRows, row.2.1.z = cfg.challenges.z) ∧
      (∀ row ∈ exec.memoryRows, row.2.1.z = cfg.challenges.z) := by
  have hload :=
    exactLanguage_challenges_loadBearing
      h.traversable.chained.semantic.toExactLanguage
  exact
    ⟨fun row hrow => (hload.1 row hrow).2,
      fun row hrow => (hload.2 row hrow).1⟩

/-- The exact public compute BFS rows inherit the tree-level realization proof. -/
theorem ExactExecutionNounRealization.computeRows
    {q : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ExactExecutionNounRealization q cfg exec) :
    ComputePublicRowsNounRealization q exec.computePublicRows := by
  rw [← exec.computePublicTree_bfs]
  exact h.computeTree

/-- The exact memory BFS rows inherit the forest-level realization proof definitionally. -/
theorem ExactExecutionNounRealization.memoryRows
    {q : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ExactExecutionNounRealization q cfg exec) :
    MemoryPublicRowsNounRealization q exec.memoryRows := by
  exact h.memoryForest

/-- Every authoritative memory root has a recursively assembled bounded noun realization. -/
theorem NounRealizedTraversableChainedSemanticExactLanguage.memory_root_realized
    {q : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : NounRealizedTraversableChainedSemanticExactLanguage q cfg exec)
    {tree : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (htree : tree ∈ exec.memoryForest) :
    FPRealized cfg.challenges.z q (memoryTreeRootFP tree) := by
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
  have hstructure :=
    MemoryFingerprintStructure.of_rvtWithArity
      cfg.challenges.z tree
      (h.traversable.memory_topology tree htree) hseed
  exact hstructure.root_realized
    h.traversable.chained.z_ne_zero
    (h.nounRealization.memoryLeaves tree htree)


namespace NounRealizationCounterRegression

instance prime17 : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- A legal characteristic-17 extension field, large enough to contain values outside the prime
subfield while satisfying the production `char > 11` state-tag condition. -/
abbrev K289 := GaloisField 17 2

noncomputable local instance : Fintype K289 := Fintype.ofFinite K289

theorem K289_card : Fintype.card K289 = 289 := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (GaloisField 17 2) = 289
  rw [GaloisField.card (p := 17) (n := 2) (by norm_num)]
  norm_num

theorem legal_stateTagChar : NodeEncoding.StateTagChar K289 :=
  NodeEncoding.stateTagChar_of_charP 17 (by omega)

noncomputable def primeSubfieldValues : Finset K289 :=
  (Finset.range 17).image (fun k : ℕ => (k : K289))

theorem exists_outside_primeSubfieldValues :
    ∃ v : K289, v ∉ primeSubfieldValues := by
  classical
  by_contra h
  have hall : ∀ v : K289, v ∈ primeSubfieldValues := by
    intro v
    by_contra hv
    exact h ⟨v, hv⟩
  have hsub :
      (Finset.univ : Finset K289) ⊆ primeSubfieldValues :=
    fun v _ => hall v
  have hcard := Finset.card_le_card hsub
  have hsmall : primeSubfieldValues.card ≤ 17 := by
    unfold primeSubfieldValues
    calc
      ((Finset.range 17).image (fun k : ℕ => (k : K289))).card
          ≤ (Finset.range 17).card := Finset.card_image_le
      _ = 17 := Finset.card_range 17
  rw [Finset.card_univ, K289_card] at hcard
  omega

noncomputable def badLeaf : K289 :=
  Classical.choose exists_outside_primeSubfieldValues

theorem badLeaf_not_mem : badLeaf ∉ primeSubfieldValues :=
  Classical.choose_spec exists_outside_primeSubfieldValues

theorem badLeaf_no_natCast (k : ℕ) : (k : K289) ≠ badLeaf := by
  intro hk
  apply badLeaf_not_mem
  unfold primeSubfieldValues
  apply Finset.mem_image.mpr
  refine ⟨k % 17, Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)), ?_⟩
  rw [CharP.natCast_eq_natCast_mod K289 17] at hk
  exact hk

theorem enc_leaf_at_one_is_natCast :
    ∀ n : Noun, ∃ k : ℕ,
      (GlobalCarryRecognizer.enc (1 : K289) n).leaf = (k : K289) := by
  intro n
  induction n with
  | atom k =>
      refine ⟨k, ?_⟩
      rw [GlobalCarryRecognizer.enc_atom]
      rfl
  | cell left right ihLeft ihRight =>
      obtain ⟨leftCast, hleft⟩ := ihLeft
      obtain ⟨rightCast, hright⟩ := ihRight
      refine ⟨leftCast + rightCast, ?_⟩
      rw [GlobalCarryRecognizer.enc_cons (by norm_num : (1 : K289) ≠ 0)]
      simp only [ComputeTable.FP.cons, GlobalCarryRecognizer.enc_size]
      norm_num
      have hleft' :
          (NPR.listPoly (NPR.leafF (K := K289) left)).eval 1 =
            (leftCast : K289) := by
        simpa [GlobalCarryRecognizer.enc] using hleft
      have hright' :
          (NPR.listPoly (NPR.leafF (K := K289) right)).eval 1 =
            (rightCast : K289) := by
        simpa [GlobalCarryRecognizer.enc] using hright
      rw [hleft', hright']

noncomputable def badFP : ComputeTable.FP K289 :=
  ⟨1, 0, badLeaf⟩

theorem badFP_no_noun_preimage :
    ¬ ∃ n : Noun, GlobalCarryRecognizer.enc (1 : K289) n = badFP := by
  rintro ⟨n, hn⟩
  obtain ⟨k, hk⟩ := enc_leaf_at_one_is_natCast n
  have hleaf := congrArg ComputeTable.FP.leaf hn
  simp [badFP] at hleaf
  exact badLeaf_no_natCast k (hk.symm.trans hleaf)

theorem badFP_not_realized (q : ℕ) :
    ¬ FPRealized (1 : K289) q badFP := by
  rintro ⟨n, -, hn⟩
  exact badFP_no_noun_preimage ⟨n, hn⟩

noncomputable def badInputs : MemoryTable.Inputs K289 :=
  ⟨1, 0, 0⟩

noncomputable def badPub : MemoryTable.Pub K289 where
  st := .halt
  pt := { noun := badFP, indicator := 0, counts := 0 }
  lc := MemoryTable.Cell.zero
  rc := MemoryTable.Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := ComputeTable.MemRec.zero
  ipre := 0
  icur := 0

noncomputable def badRow :
    MemoryTable.MState × MemoryTable.DTmem K289 :=
  (.halt, (badInputs, badPub))

/-- The production row verifier accepts the legal-characteristic field row; the missing premise
is specifically Nat-valued noun existence. -/
theorem badRow_publicAccepted :
    MemoryPublicRowAccepted badRow := by
  refine ⟨rfl, ?_⟩
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp [badRow, badInputs, badPub, badFP, MemoryTable.eqBlk,
      MemoryTable.Cell.zero, ComputeTable.MemRec.zero]
  · simp [badRow, badPub, MemoryTable.interV]

noncomputable def badTree :
    NTree (MemoryTable.MState × MemoryTable.DTmem K289) :=
  .node badRow []

/-- The same row is a production `Fmem` leaf, so this is not merely a malformed field tuple. -/
theorem badTree_rvt :
    RVT (MemoryTable.Fmem (K := K289)) badTree := by
  unfold badTree RVT
  have hF : MemoryTable.Fmem badRow (fun _ => none) := by
    refine ⟨rfl, badRow_publicAccepted.2, ?_, ?_⟩
    · intro i
      simp [badRow, MemoryTable.fanoutMem]
    · intro i hi
      simp [badRow, MemoryTable.fanoutMem] at hi
  exact ⟨hF, by simp, ⟨fun _ => hF, fun _ => rfl⟩⟩

theorem badRow_not_nounRealized (q : ℕ) :
    ¬ MemoryPublicRowNounRealization q badRow := by
  intro h
  apply badFP_not_realized q
  simpa [badRow, badInputs, badPub] using h.parent.1

end NounRealizationCounterRegression

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.MemoryFingerprintStructure.root_realized
#print axioms Nock.NockVMROM.Thm54.MemoryFingerprintStructure.of_rvtWithArity
#print axioms Nock.NockVMROM.Thm54.FPRealizationWitness.unique
#print axioms Nock.NockVMROM.Thm54.NounRealizedTraversableChainedSemanticExactLanguage.memory_root_realized
#print axioms Nock.NockVMROM.Thm54.NounRealizationCounterRegression.badTree_rvt
#print axioms Nock.NockVMROM.Thm54.NounRealizationCounterRegression.badRow_not_nounRealized
