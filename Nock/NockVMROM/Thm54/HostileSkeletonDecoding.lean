/-
  Nock/NockVMROM/Thm54/HostileSkeletonDecoding.lean

  **Decode the skeleton from a committed memory forest.**

  A hostile trace commits NPR triples in `𝕂³`, not nouns.
  `decodeNoun` reads a noun off each committed tree by the NPR recursion
  (`Lem:NPR_decomp` `:1218`, `Thm:Noun_Validation` `:1268`): halt leaves from the
  typed atom value, cells from children, pass-through at `read_root`/`verify_child`.

  `hostileCensus` lists every pair of decoded BFS-node nouns so
  `collisionFailureEvent` (`lem:ion_univariate_sec` `:1188`) is that set.
  Cardinality is a row-count majorant (`MC`): `|census| ≤ M²`.
-/
import Nock.NockVMROM.Thm54.NounRealization
import Nock.NockVMROM.Thm54.SemanticStrategy
import Nock.NockVMROM.Thm54.SizeWindowCounting
import Nock.NockVMROM.Thm54.JointSoundness
import Nock.GlobalCarryRecognizer

namespace Nock.NockVMROM.Thm54.HostileSkeletonDecoding

open Nock
open Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open scoped Classical
attribute [local instance] Classical.propDecidable

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## §1  `decodeNoun` -/

/-- The `ℕ` preimage of a committed leaf scalar inside `[0, q)`.  Seed-free. -/
def leafAtomOf (q : ℕ) (v : K) : ℕ :=
  if h : ∃ k : ℕ, k < q ∧ (k : K) = v then h.choose else 0

theorem leafAtomOf_lt {q : ℕ} {v : K} (h : ∃ k : ℕ, k < q ∧ (k : K) = v) :
    leafAtomOf q v < q := by
  rw [leafAtomOf, dif_pos h]
  exact h.choose_spec.1

theorem leafAtomOf_cast {q : ℕ} {v : K} (h : ∃ k : ℕ, k < q ∧ (k : K) = v) :
    ((leafAtomOf q v : ℕ) : K) = v := by
  rw [leafAtomOf, dif_pos h]
  exact h.choose_spec.2

theorem leafAtomOf_lt_of_pos {q : ℕ} (hq : 0 < q) (v : K) :
    leafAtomOf q v < q := by
  unfold leafAtomOf
  split_ifs with h
  · exact h.choose_spec.1
  · exact hq

/-- The noun a committed memory tree stands for.  Seed-free. -/
def decodeNoun (q : ℕ) :
    NTree (MemoryTable.MState × MemoryTable.DTmem K) → Noun
  | .node (.halt, data) [] =>
      Noun.atom (leafAtomOf q data.2.pt.noun.leaf)
  | .node (.decompose, _) [left, right] =>
      Noun.cell (decodeNoun q left) (decodeNoun q right)
  | .node (.read_root, _) [child] => decodeNoun q child
  | .node (.verify_child, _) [child] => decodeNoun q child
  | _ => Noun.atom 0

/-- BFS-order decoded nouns of a forest.  One entry per committed memory row. -/
def decodedNodes (q : ℕ)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))) :
    List Noun :=
  (bfsForest forest).map (decodeNoun q)

/-- **`decode_fingerprint`.**  Under the chip-implied fingerprint structure
and bounded halt leaves, the committed triple is `fn` of the decoded noun. -/
theorem decode_fingerprint {z : K} (hz : z ≠ 0) {q : ℕ}
    {t : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hstructure : MemoryFingerprintStructure z t)
    (hleaves : MemoryLeafAtomsRealized q t) :
    GlobalCarryRecognizer.enc z (decodeNoun q t) = memoryTreeRootFP t := by
  induction hstructure with
  | halt data atomShape =>
      have hex : ∃ k : ℕ, k < q ∧ (k : K) = data.2.pt.noun.leaf := hleaves
      rw [decodeNoun, GlobalCarryRecognizer.enc_atom]
      exact ComputeTable.FP.ext atomShape.1.symm atomShape.2.symm
        (leafAtomOf_cast hex)
  | decompose data left right consEq hL hR ihL ihR =>
      have ⟨hleavesL, hleavesR⟩ := hleaves
      rw [decodeNoun, GlobalCarryRecognizer.enc_cons hz, ihL hleavesL, ihR hleavesR]
      exact consEq.symm
  | readRoot data child passEq childStructure ih =>
      rw [decodeNoun, ih hleaves]
      simpa [memoryTreeRootFP] using passEq.symm
  | verifyChild data child passEq childStructure ih =>
      rw [decodeNoun, ih hleaves]
      simpa [memoryTreeRootFP] using passEq.symm

theorem decodeNoun_leaves_le {z : K}
    {t : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : MemoryFingerprintStructure z t) {q : ℕ}
    (_hleaves : MemoryLeafAtomsRealized q t) :
    (decodeNoun q t).leaves ≤ NTree.size t := by
  induction h with
  | halt data atomShape =>
      simp [decodeNoun, Noun.leaves, NTree.size]
  | decompose data left right consEq hL hR ihL ihR =>
      have ⟨hleavesL, hleavesR⟩ := _hleaves
      have hL' := ihL hleavesL
      have hR' := ihR hleavesR
      have hsz :
          NTree.size (.node (.decompose, data) [left, right])
            = 1 + NTree.size left + NTree.size right := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        exact (add_assoc 1 left.size right.size).symm
      simp only [decodeNoun, Noun.leaves] at hL' hR' ⊢
      omega
  | readRoot data child passEq childStructure ih =>
      have hih := ih _hleaves
      simp only [decodeNoun] at hih ⊢
      exact hih.trans (by simp [NTree.size])
  | verifyChild data child passEq childStructure ih =>
      have hih := ih _hleaves
      simp only [decodeNoun] at hih ⊢
      exact hih.trans (by simp [NTree.size])

/-! ## §2  `hostileCensus` -/

/-- All ordered pairs `(i, j)` with `i.1 < j.1`.  Length `≤ n²`. -/
def pairsBelow (n : ℕ) : List (Fin n × Fin n) :=
  ((List.ofFn fun i : Fin n => List.ofFn fun j : Fin n => (i, j)).flatten).filter
    fun p => p.1.1 < p.2.1

theorem pairsBelow_length_le (n : ℕ) : (pairsBelow n).length ≤ n * n := by
  unfold pairsBelow
  have hflat :
      ((List.ofFn fun i : Fin n => List.ofFn fun j : Fin n => (i, j)).flatten).length
        = n * n := by
    rw [List.length_flatten, List.map_ofFn]
    simp [List.length_ofFn, List.sum_ofFn]
  have hfilt :=
    List.length_filter_le
      (p := fun p : Fin n × Fin n => p.1.1 < p.2.1)
      ((List.ofFn fun i : Fin n => List.ofFn fun j : Fin n => (i, j)).flatten)
  exact hfilt.trans (Nat.le_of_eq hflat)

/-- Comparison census over a list of decoded nouns. -/
def hostileCensusOfNouns (Λ : ℕ) (xs : List Noun)
    (hbound : ∀ n ∈ xs, n.leaves ≤ Λ) : ComparisonCensus Λ where
  count := (pairsBelow xs.length).length
  pair i :=
    let p := (pairsBelow xs.length).get i
    (xs.get p.1, xs.get p.2)
  leaves_bounded i := by
    let p := (pairsBelow xs.length).get i
    exact ⟨hbound (xs.get p.1) (List.get_mem _ _),
      hbound (xs.get p.2) (List.get_mem _ _)⟩

theorem hostileCensusOfNouns_count_le (Λ : ℕ) (xs : List Noun)
    (hbound : ∀ n ∈ xs, n.leaves ≤ Λ) :
    (hostileCensusOfNouns Λ xs hbound).count ≤ xs.length * xs.length := by
  simpa [hostileCensusOfNouns] using pairsBelow_length_le xs.length

/-- Forest form: decoded BFS nouns, window `Λ`. -/
def hostileCensus (q Λ : ℕ)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K)))
    (hbound : ∀ n ∈ decodedNodes q forest, n.leaves ≤ Λ) :
    ComparisonCensus Λ :=
  hostileCensusOfNouns Λ (decodedNodes q forest) hbound

/-- **MC majorant.**  `|hostileCensus| ≤ M²` with `M = |bfsForest forest|`. -/
theorem hostileCensus_count_le (q Λ : ℕ)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K)))
    (hbound : ∀ n ∈ decodedNodes q forest, n.leaves ≤ Λ) :
    (hostileCensus q Λ forest hbound).count
      ≤ (bfsForest forest).length * (bfsForest forest).length := by
  simpa [hostileCensus, decodedNodes] using
    hostileCensusOfNouns_count_le Λ (decodedNodes q forest) hbound

/-- Negative control: a listed pair whose NPR bits differ and whose
fingerprints collide sits in `badSeeds`. -/
theorem collision_mem_badSeeds
    {Λ : ℕ} (C : ComparisonCensus Λ) [Fintype K] [DecidableEq K]
    (z : K) (i : Fin C.count)
    (hbits :
      (NPR.leafF (K := K) (C.pair i).1, NPR.dyckBits (K := K) (C.pair i).1)
        ≠ (NPR.leafF (K := K) (C.pair i).2, NPR.dyckBits (K := K) (C.pair i).2))
    (hfn : NPR.fn (C.pair i).1 z = NPR.fn (C.pair i).2 z) :
    z ∈ C.badSeeds (K := K) := by
  refine (ComparisonCensus.mem_badSeeds_iff (K := K) C z).2 ⟨i, ?_⟩
  intro hsep
  exact hsep hbits hfn


structure ComputeJoin where
  computeTree : NTree ComputeRowSkeleton

structure ComputeJoinSound (z : K) (join : ComputeJoin)
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Prop where
  sampledSeed : cfg.challenges.z = z
  computeTree : ComputeTreeBinds z join.computeTree exec.computeTree

/-- Paper-`⊥` record halves are unconstrained on the deployed chip. -/
structure RecordHalfJoin where
  readRootChild : Noun
  verifyChildRoot : Noun

def RecordHalfJoin.placeholder : RecordHalfJoin where
  readRootChild := Noun.atom 0
  verifyChildRoot := Noun.atom 0

/-- Forest noun whose committed `pt.noun` equals `fp`.  Same `find?` as
`StrategyOfTraces.nounByFP`.  Misses (including the empty forest) are
`atom 0`. -/
def nounByFP (q : ℕ)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K)))
    (fp : ComputeTable.FP K) : Noun :=
  match (bfsForest forest).find? (fun t => t.label.2.2.pt.noun = fp) with
  | some t => decodeNoun q t
  | none => Noun.atom 0

theorem nounByFP_nil (q : ℕ) (fp : ComputeTable.FP K) :
    nounByFP q [] fp = Noun.atom 0 := by
  simp [nounByFP, bfsForest_nil]

/-- Memory-row skeleton of one committed tree.  Paper-`⊥` halves
are filled by `nounByFP` of the joined record fingerprint; `axis` is
the Nat preimage of the record's axis. -/
def decodeMemoryRowIn (q : ℕ)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))) :
    NTree (MemoryTable.MState × MemoryTable.DTmem K) → MemoryRowSkeleton
  | .node (.halt, data) _ =>
      { state := .halt
        parent := Noun.atom (leafAtomOf q data.2.pt.noun.leaf)
        haltAtom := fun _ => leafAtomOf q data.2.pt.noun.leaf
        haltParent := fun _ => rfl
        child := fun i hi => False.elim (by
          simp [MemoryTable.fanoutMem] at hi)
        memoryRecord := fun h => False.elim (by
          simp [memoryMemRecKind] at h) }
  | .node (.decompose, _) [left, right] =>
      { state := .decompose
        parent := Noun.cell (decodeNoun q left) (decodeNoun q right)
        haltAtom := fun h => nomatch h
        haltParent := fun h => nomatch h
        child := fun i _hi =>
          if i.val = 0 then decodeNoun q left else decodeNoun q right
        memoryRecord := fun h => False.elim (by
          simp [memoryMemRecKind] at h) }
  | .node (.read_root, data) [child] =>
      { state := .read_root
        parent := decodeNoun q child
        haltAtom := fun h => nomatch h
        haltParent := fun h => nomatch h
        child := fun _ _ => decodeNoun q child
        memoryRecord := fun _ =>
          { root := decodeNoun q child
            child := nounByFP q forest data.2.mem.child
            axis := leafAtomOf q data.2.mem.axis } }
  | .node (.verify_child, data) [child] =>
      { state := .verify_child
        parent := decodeNoun q child
        haltAtom := fun h => nomatch h
        haltParent := fun h => nomatch h
        child := fun _ _ => decodeNoun q child
        memoryRecord := fun _ =>
          { root := nounByFP q forest data.2.mem.root
            child := decodeNoun q child
            axis := leafAtomOf q data.2.mem.axis } }
  | _ =>
      { state := .halt
        parent := Noun.atom 0
        haltAtom := fun _ => 0
        haltParent := fun _ => rfl
        child := fun i hi => False.elim (by
          simp [MemoryTable.fanoutMem] at hi)
        memoryRecord := fun h => False.elim (by
          simp [memoryMemRecKind] at h) }

def decodeMemoryRow (q : ℕ) :
    NTree (MemoryTable.MState × MemoryTable.DTmem K) → MemoryRowSkeleton :=
  decodeMemoryRowIn q []

@[simp] theorem decodeMemoryRowIn_readRoot_state (q : ℕ)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K)))
    (data : MemoryTable.DTmem K)
    (child : NTree (MemoryTable.MState × MemoryTable.DTmem K)) :
    (decodeMemoryRowIn q forest (.node (.read_root, data) [child])).state =
      .read_root :=
  rfl

@[simp] theorem decodeMemoryRowIn_verifyChild_state (q : ℕ)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K)))
    (data : MemoryTable.DTmem K)
    (child : NTree (MemoryTable.MState × MemoryTable.DTmem K)) :
    (decodeMemoryRowIn q forest (.node (.verify_child, data) [child])).state =
      .verify_child :=
  rfl

def decodeMemoryTree (q : ℕ)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))) :
    NTree (MemoryTable.MState × MemoryTable.DTmem K) →
      NTree MemoryRowSkeleton
  | .node lbl ch =>
      .node (decodeMemoryRowIn q forest (.node lbl ch))
        (ch.map (decodeMemoryTree q forest))

def decodedMemoryForest (q : ℕ)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))) :
    List (NTree MemoryRowSkeleton) :=
  forest.map (decodeMemoryTree q forest)

def decodedSkeleton (q : ℕ) (join : ComputeJoin)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))) :
    SemanticSkeleton where
  computeTree := join.computeTree
  memoryForest := decodedMemoryForest q forest

/-- Compute half of `decoded_binds`. -/
theorem decoded_binds_compute
    {z : K} {join : ComputeJoin}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hjoin : ComputeJoinSound z join cfg exec) :
    ComputeTreeBinds z
        (decodedSkeleton (K := K) (q := 0) join []).computeTree
      exec.computeTree :=
  hjoin.computeTree

theorem decodedMemoryForest_length (q : ℕ)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))) :
    (decodedMemoryForest q forest).length = forest.length := by
  simp [decodedMemoryForest]

/-! ## §4  Boundedness -/

/-- Every decoded noun lands in `[0, q)` when `0 < q`. -/
theorem decodeNoun_bounded {q : ℕ} (hq : 0 < q)
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K)) :
    FieldEmbedding.BoundedBy q (decodeNoun q t) := by
  fun_induction decodeNoun q t
  · simp [FieldEmbedding.BoundedBy]; exact leafAtomOf_lt_of_pos hq _
  · rename_i ihL ihR
    simp [FieldEmbedding.BoundedBy]; exact ⟨ihL, ihR⟩
  · rename_i ih; simpa [FieldEmbedding.BoundedBy] using ih
  · rename_i ih; simpa [FieldEmbedding.BoundedBy] using ih
  · simpa [FieldEmbedding.BoundedBy] using hq

theorem nounByFP_bounded {q : ℕ} (hq : 0 < q)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K)))
    (fp : ComputeTable.FP K) :
    FieldEmbedding.BoundedBy q (nounByFP q forest fp) := by
  unfold nounByFP
  split
  · exact decodeNoun_bounded hq _
  · simpa [FieldEmbedding.BoundedBy] using hq

theorem decodeMemoryRowIn_bounded {q : ℕ} (hq : 0 < q)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K)))
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K)) :
    MemoryRowSkeleton.BoundedBy q (decodeMemoryRowIn q forest t) := by
  unfold decodeMemoryRowIn
  split
  · refine ⟨?_, ?_, ?_⟩
    · simp; exact leafAtomOf_lt_of_pos hq _
    · intro i hi
      simp [MemoryTable.fanoutMem] at hi
    · intro h
      simp [memoryMemRecKind] at h
  · rename_i left right
    refine ⟨?_, ?_, ?_⟩
    · simp
      exact ⟨decodeNoun_bounded hq left, decodeNoun_bounded hq right⟩
    · intro i _hi
      simp
      split_ifs
      · exact decodeNoun_bounded hq left
      · exact decodeNoun_bounded hq right
    · intro h
      simp [memoryMemRecKind] at h
  · rename_i data child
    refine ⟨?_, ?_, ?_⟩
    · simp; exact decodeNoun_bounded hq child
    · intro i _hi
      simp; exact decodeNoun_bounded hq child
    · intro _h
      simp [MemRecSkeleton.BoundedBy]
      exact ⟨decodeNoun_bounded hq child, nounByFP_bounded hq forest _⟩
  · rename_i data child
    refine ⟨?_, ?_, ?_⟩
    · simp; exact decodeNoun_bounded hq child
    · intro i _hi
      simp; exact decodeNoun_bounded hq child
    · intro _h
      simp [MemRecSkeleton.BoundedBy]
      exact ⟨nounByFP_bounded hq forest _, decodeNoun_bounded hq child⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp; exact hq
    · intro i hi
      simp [MemoryTable.fanoutMem] at hi
    · intro h
      simp [memoryMemRecKind] at h

theorem decodeMemoryRow_bounded {q : ℕ} (hq : 0 < q)
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K)) :
    MemoryRowSkeleton.BoundedBy q (decodeMemoryRow q t) :=
  decodeMemoryRowIn_bounded hq [] t

theorem decodeMemoryTree_inTree_bounded {q : ℕ} (hq : 0 < q)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K)))
    {t : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    {node : NTree MemoryRowSkeleton}
    (h : InTree (decodeMemoryTree q forest t) node) :
    node.label.BoundedBy q := by
  let P := fun t : NTree (MemoryTable.MState × MemoryTable.DTmem K) =>
    ∀ node, InTree (decodeMemoryTree q forest t) node →
      MemoryRowSkeleton.BoundedBy q node.label
  suffices P t from this node h
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro lbl children ih node' h'
    simp only [decodeMemoryTree] at h'
    cases h' with
    | here =>
        exact decodeMemoryRowIn_bounded hq forest (.node lbl children)
    | sub hs hrest =>
        rcases List.mem_map.mp hs with ⟨t', ht', rfl⟩
        exact ih t' ht' node' hrest
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

structure JoinBounded (q : ℕ) (join : ComputeJoin) : Prop where
  compute :
    ∀ node, InTree join.computeTree node →
      ComputeRowSkeleton.BoundedBy q node.label

/-- Size-window nouns live on compute rows `s3`/`s4`/`s6`. -/
structure JoinWindow (join : ComputeJoin) (Λ : ℕ) : Prop where
  leaves :
    ∀ n ∈ SizeWindowCounting.skeletonSizeWindowNouns
        ⟨join.computeTree, []⟩, n.leaves ≤ Λ

theorem sizeWindow_of_join {Λ : ℕ} (join : ComputeJoin) (q : ℕ)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K)))
    (h : JoinWindow join Λ) :
    SizeWindowCounting.SizeWindowNounsBoundedBy
      (decodedSkeleton q join forest) Λ := by
  intro n hn
  have : n ∈ SizeWindowCounting.skeletonSizeWindowNouns
      ⟨join.computeTree, []⟩ := by
    simpa [decodedSkeleton, SizeWindowCounting.skeletonSizeWindowNouns,
      SemanticStrategy.computeSkeletonRows] using hn
  exact h.leaves n this

/-- Memory half of `decodedSkeleton.BoundedBy q` is by construction
(`leafAtomOf` lands in `[0, q)`).  Compute half is `JoinBounded`. -/
theorem decodedSkeleton_bounded {q : ℕ} (hq : 0 < q)
    (join : ComputeJoin) (hjoin : JoinBounded q join)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))) :
    SemanticSkeleton.BoundedBy q (decodedSkeleton q join forest) where
  computeRows := by
    refine List.forall_iff_forall_mem.mpr ?_
    intro s hs
    simp [decodedSkeleton, computeSkeletonRows] at hs
    rcases hs with ⟨node, hnode, rfl⟩
    obtain ⟨c, hc, hIn⟩ := (mem_bfsForest [join.computeTree] node).1 hnode
    simp only [List.mem_singleton] at hc
    subst hc
    exact hjoin.compute node hIn
  memoryRows := by
    refine List.forall_iff_forall_mem.mpr ?_
    intro s hs
    simp [decodedSkeleton, memorySkeletonRows] at hs
    rcases hs with ⟨node, hnode, rfl⟩
    obtain ⟨tree, htree, hIn⟩ :=
      (mem_bfsForest (decodedMemoryForest q forest) node).1 hnode
    simp [decodedMemoryForest] at htree
    rcases htree with ⟨t, _ht, rfl⟩
    exact decodeMemoryTree_inTree_bounded hq forest hIn
  memoryTrees := by
    intro tree htree node hnode
    simp [decodedSkeleton, decodedMemoryForest] at htree
    rcases htree with ⟨t, _ht, rfl⟩
    exact decodeMemoryTree_inTree_bounded hq forest hnode

end

#print axioms Nock.NockVMROM.Thm54.HostileSkeletonDecoding.decode_fingerprint
#print axioms Nock.NockVMROM.Thm54.HostileSkeletonDecoding.hostileCensus_count_le
#print axioms Nock.NockVMROM.Thm54.HostileSkeletonDecoding.collision_mem_badSeeds
#print axioms Nock.NockVMROM.Thm54.HostileSkeletonDecoding.decoded_binds_compute
#print axioms Nock.NockVMROM.Thm54.HostileSkeletonDecoding.decodedSkeleton_bounded

end Nock.NockVMROM.Thm54.HostileSkeletonDecoding
